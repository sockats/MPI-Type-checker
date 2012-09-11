/**
 * \file
 * MPI Type Checker.
 * This is implemented as a plugin for the LLVM/clang compiler.
 *
 */

/*Some comments that contain std::cout can be used for debugging 
 purposes. In addition, other print functions such as st_tree_print can be found
 commented and can be used for ddbugging as well*/

#include <cstdio>
#include <sstream>
#include <stack>
#include <map>
#include <iostream> 
#include <cstring>

#include "/home/socrates/llvm/tools/clang/include/clang/AST/ASTConsumer.h"
#include "/home/socrates/llvm/tools/clang/include/clang/AST/DeclVisitor.h"
#include "/home/socrates/llvm/tools/clang/include/clang/AST/StmtVisitor.h"

#include "/home/socrates/llvm/tools/clang/include/clang/Frontend/FrontendPluginRegistry.h"
#include "/home/socrates/llvm/tools/clang/include/clang/Frontend/CompilerInstance.h"

#include "st_node.h"
#include "canonicalise.h"
#include "scribble/print.h"
#include "scribble/project.h"

extern "C" {
  extern int yyparse(st_tree *tree);
  extern FILE *yyin;
}


using namespace clang;
using namespace llvm;

namespace {
  
  class MPITypeCheckingConsumer : 
      public ASTConsumer,
      public DeclVisitor<MPITypeCheckingConsumer>,
      public StmtVisitor<MPITypeCheckingConsumer> {
  
    protected:

    typedef DeclVisitor<MPITypeCheckingConsumer> BaseDeclVisitor;
    typedef StmtVisitor<MPITypeCheckingConsumer> BaseStmtVisitor;

    // AST-related fields.
    ASTContext    *context_;
    SourceManager *src_mgr_;
    TranslationUnitDecl *tu_decl_;
    Decl          *current_decl_;

    // Recursion counter.
    int recur_counter;
    int caseState, ifState;
    int breakStmt_count, branch_count, outbranch_count, chain_count;
    
    //scrible tree
    st_tree *scribble_tree_;
    
    std::string scribbleFilePath;
    
    //number of processors
    int num_of_processors;
    //current binary operator
    std::string bin_op;
    
    //current rank
    int cur_rank;
    
    //true if have to update all endpoint trees
    bool all_ranks;
    
    //is true when if stmt is in use
    bool isIfStmt;
    //is true when we are in an "else if"
    bool isElseIfStmt;
    //is true when "else if" stmt is in use - true until lvlOfIndent in IF handler does not change
    // on enrty point of IF ELSE Stmt
    bool isEntryLvlElseIfStmt;
    //is true when "else if" stmt is in use - breaks at some point before leaving ELSE
    bool isEntryLvlElseStmt;
    
    //is true when updateTree function call itself
    bool recurCall_updateTreeFun;
    
    //level of indentation
    int lvlOfIndent;
    
    //is true when we are in main function
    bool visitNow;
    
    //when we have to update all the ranks (ranks taken form parent IF) is an ELSE stmt
    bool updateAllInElse;
    
    //put root node under choice if needed
    bool putRootUnderChoice;
   
    //vector with endpoint trees and stack
    std::vector<st_tree*> end_trees;
    std::vector< std::stack<st_node*> > appendto_nodes;
    
    //stack that keeps list that contains ranks visited in if statememts
    std::stack< std::list<int> > stackOfRanks;
    
    //this vector keeps the names of variables holding "ranks" (processors ids)
    std::vector<std::string> rankNames;
    
    //current ranks on each level of indentation
    std::stack< std::list<int> > stackRankOnLvlOfInd;
    
    //keep if choice nodes empty in each level
    std::stack< std::vector<st_node*> > stackOfChoiceNodes;
    
    //the root of a collective opearator
    int collectiveOperRoot;
    
    bool isCollectiveOper;
    
    public:

      virtual void Initialise(ASTContext &ctx, int num_of_proc, std::string scrbl_filePath) {
        context_ = &ctx;
	src_mgr_ = &context_->getSourceManager();
        tu_decl_ = context_->getTranslationUnitDecl();
	
	num_of_processors = num_of_proc;
	scribbleFilePath = scrbl_filePath;
	
	all_ranks = true;
	isIfStmt = false;
	isElseIfStmt = false;
	isEntryLvlElseIfStmt = false;
	isEntryLvlElseStmt = false;
	recurCall_updateTreeFun = false;
	visitNow = false;
	updateAllInElse = false;
	putRootUnderChoice = false;
	lvlOfIndent = 0;
	isCollectiveOper = false;
	
	//make vectors to have size same as the number of processors
	end_trees.resize(num_of_processors);
	appendto_nodes.resize(num_of_processors);
	
	//an int that is used only in the iteration below to give to trees names
	int rank_int = 0;
	
	for (std::vector<st_tree*>::iterator it = end_trees.begin(); it != end_trees.end(); ++it) {
	     std::ostringstream oss;
	     std::string tmp_str;
	     //current rank - it will be used in tree name
	     std::string tmp_str_currentRank;

	     //convert int to string
	     oss << rank_int;
	     tmp_str += oss.str();	     
	     tmp_str_currentRank = "Tree of processor with rank " +  tmp_str;
	     
	     *it = (st_tree*)malloc(sizeof(st_tree));
	     st_tree_init(*it);
	     st_tree_set_name(*it, tmp_str_currentRank.c_str());
	     rank_int++;
	}
	
	      //if no MPI_int uncomment this code and comment the code on MPI_Init routine below
	      /*std::vector<st_tree*>::iterator it1 = end_trees.begin();
	      std::vector< std::stack<st_node*> >::iterator it2 = appendto_nodes.begin();
	      
	      while(it1 != end_trees.end() && it2 != appendto_nodes.end())
	      {	  
		  //copy stack from vector to a temporary stack
		  std::stack<st_node*> tmp_stack = *it2;
		  st_node* tmp_st_node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_ROOT);;
		  
		  (*it1)->root = tmp_st_node;
		  tmp_stack.push(tmp_st_node);
		  //update stack
		  *it2 = tmp_stack;
		 
		  it1++;
		  it2++;
	      }*/
   
        // Recursion label generation.
        recur_counter = 0;

      } // Initialise()


      virtual void HandleTranslationUnit(ASTContext &ctx) {
        TranslationUnitDecl *tu_decl = context_->getTranslationUnitDecl();

        for (DeclContext::decl_iterator
             iter = tu_decl->decls_begin(), iter_end = tu_decl->decls_end();
             iter != iter_end; ++iter) {
          // Walk the AST to get source code ST tree.
          Decl *decl = *iter;
	
          BaseDeclVisitor::Visit(decl);
	}
	
	// Scribble protocol.
        st_node_canonicalise(scribble_tree_->root);
	
	
	//refactor, canonicalise session trees (rank trees)
        for (std::vector<st_tree*>::iterator it = end_trees.begin(); it != end_trees.end(); ++it) {
	  st_node_refactor((*it) -> root);
	  st_node_canonicalise((*it) -> root);
	}
	
	std::cout << "\n";
	
	int tree_num = 0;
	
	bool typecheckingSuccessful = false;
	
	//typecheck
	for (std::vector<st_tree*>::iterator it = end_trees.begin(); it != end_trees.end(); ++it) 
	{ 
	  unsigned diagId;
	    
	   std::ostringstream tmp_oss_treeNum;
	   std::string tmp_str_treeNum;
	   
	   //session tree number convert from int to string
	   tmp_oss_treeNum << tree_num;
           tmp_str_treeNum += tmp_oss_treeNum.str();
	    
	   //for each role in scribble file
	   for (int i = 0; i < scribble_tree_->info->nrole; i++)
	   {
	     //scribble file does not have numbers for rank so we use R1,R2, R3, ..., Rn and so we get the number after "R"
	     std::string tmp_str = scribble_tree_->info->roles[i];
	     std::string rank_role = tmp_str.substr(1, tmp_str.size()-1);
	     
	     //rank/role in scribble file matches a end-point tree/end-point program
	     //compare the end-point protocols with the end-point programs
	     if (strcmp(rank_role.c_str(), tmp_str_treeNum.c_str()) == 0)
	     {
	        //note- always put scribble tree as first argument in this function
		st_tree *end_pointProt = scribble_project(scribble_tree_, scribble_tree_->info->roles[i]);
		end_pointProt->info->name = scribble_tree_->info->roles[i];
		
		st_node_reset_markedflag((*it)->root);
	        st_node_reset_markedflag(end_pointProt->root);
		
		st_node_refactor(end_pointProt->root);
	        st_node_canonicalise(end_pointProt->root);
		
		if (st_node_compare_r(end_pointProt->root, (*it)->root)) {
		 
		  if(typecheckingSuccessful == false && tree_num == 0)
		  {
		    typecheckingSuccessful = true;
		  }else if (typecheckingSuccessful == false && tree_num > 0){
		    typecheckingSuccessful = false;
		  }else{
		    typecheckingSuccessful = true;
		  }
		  
		} else {
		  // Show the error
		  std::cout << "********** Scribble tree**********" << std::endl;
		  st_tree_print(end_pointProt, 1);
		  
		  std::cout << "********** Source code tree**********" << std::endl;
		  st_tree_print(*it, 0);
		  
		  typecheckingSuccessful = false;
		}
		
		//free tree
		st_tree_free(end_pointProt);
	     }
	   }
	   
	  tree_num++;
	}
	
	
	//if deadlock free
	if(typecheckingSuccessful == true)
	{
	 std::cout << "\nType checking successful !" << std:: endl; 
	}else {
	  std::cout << "\nType checking failed, see above for error location." << std::endl; 
	}
	
	
	//free the rank trees
        for (std::vector<st_tree*>::iterator it = end_trees.begin(); it != end_trees.end(); ++it) {
	  //st_tree_print(*it, 0);
          st_tree_free(*it);
	}
	
	//free scribble tree
	st_tree_free(scribble_tree_);
      }

      /* Auxiliary functions------------------------------------------------- */
      
      //check which elements are the same in two lists and return a list with these elements
      std::list<int> checkLists(std::list<int> topList, std::list<int> bottomList)
      {
	  std::list<int> finalList;
	
	  for(std::list<int>::iterator topList_it = topList.begin(); topList_it != topList.end(); topList_it++){
	    for(std::list<int>::iterator bottomList_it = bottomList.begin(); bottomList_it != bottomList.end(); bottomList_it++){
		if(*topList_it == *bottomList_it)
		{
		  finalList.push_front(*topList_it);
		}
	    }
	  }
	  
	  finalList.sort();
	  finalList.unique();
	  
	  return finalList;
      }
      
      //check if the given number is on all lists (except the top one - when beggining the top) of the stackOfRanks stack
      bool isInStack(int rank, std::stack< std::list<int> > givenStack, bool popFirst)
      {
	std::stack< std::list<int> > tmp_stack = givenStack;
	
	int counter = 0;
	
	while(tmp_stack.size() > 0)
	{
	  //we do not need to examine the top list
	  if(counter == 0 && popFirst == true)
	  {
	      tmp_stack.pop();
	  }
	  
	  
	  std::list<int> tmp_list = tmp_stack.top();
	  
	  //if rank not found on list
	  if(isInList(tmp_list, rank) == 2)
	  {
	     return false;
	  }
	  
	 //pop to get the next list
	 tmp_stack.pop();
	 counter++;
	}
	
	return true;
      }
      
      //check if the treeNum (rank in the list are also representing tree numbers since each processor has a tree) is in list
      int isInList(std::list<int> ranks_list, int treeNum)
      {
	 //if list is empty
	 if(ranks_list.empty())
	 {
	   return 0; 
	 }
	
	 for(std::list<int>::iterator it = ranks_list.begin(); it != ranks_list.end(); it++)
	 { 
	    if(*it == treeNum)
	    {
	       // if element found on list
	       return 1;
	    }
	 }
	 
	 //if element not found on list
	 return 2;
      }
      
      //put choice node and root on rank trees
      std::vector<st_node*> putChoiceNodeAndRoot(std::vector<st_node*> choice_nodes)
      {
	st_node *node;
	  
	std::vector< std::stack<st_node *> >::iterator it1 = appendto_nodes.begin();
	  
	//put choice nodes in stack
	while(it1 != appendto_nodes.end())
	{	
	  node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_CHOICE);
          node->choice->at = "-";
	      
	  //the next line where we insert the choice node into a vector will be used later
	  choice_nodes.push_back(node);
	      
	  st_node * previous_node = (*it1).top();
	  st_node_append(previous_node, node);
	  (*it1).push(node);
	      
	   it1++;
	   //it2++;
	} 
				
	//put root node
	std::vector< std::stack<st_node *> >::iterator appto_node = appendto_nodes.begin();
	      
	while (appto_node != appendto_nodes.end())
	{	  
	   st_node* root_node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_ROOT);
	   std::stack<st_node*> tmp_stack = *appto_node;
	   st_node* previous_node = tmp_stack.top();
		  
	   st_node_append(previous_node, root_node);
	   (*appto_node).push(root_node);
		 
	   appto_node++;
	}
	
	return choice_nodes;
      }
      
      //reverses a list. Ex. [1,2] with 4 processors (0 - 3) has reversed list [0, 3]
      std::list<int> reverseList(std::list<int> visitedRanks)
      {
	std::list<int> ranksToBeVisited;
	      
	      int contains_rank;
	      
	      for (int rank=0; rank < num_of_processors; rank++) {
		contains_rank = 0;
		for (std::list<int>::iterator visRanks_it = visitedRanks.begin(); visRanks_it != visitedRanks.end(); visRanks_it++) {
		  if (*visRanks_it == rank) {
		    contains_rank = 1;
		    break;
		  }
	        }
		if (!contains_rank)
		{
		  ranksToBeVisited.push_back(rank);
		}
	      }
	      
	      //sort and remove duplicates
	      ranksToBeVisited.sort();
	      ranksToBeVisited.unique();
	      
	      return ranksToBeVisited;
      }
      
      //return the rank of a BinaryOperator statememt.
      int getRank(BinaryOperator *BO) {
	int rank;  
	
	  // get rank num. from integer (not variable - actual number, ex. 5)
	  if(isa<IntegerLiteral>(BO->getRHS())){
	    if(IntegerLiteral *IL = dyn_cast<IntegerLiteral>(BO->getRHS()))
	    {   
	      const uint64_t *tmp_rank = IL->getValue().getRawData();
	      rank = static_cast<int>(*tmp_rank);
	      
	      return rank;
	    }
	  }
	  
	  
	  //get rank num. from a variable
	  if(isa<ImplicitCastExpr>(BO->getRHS())){
	    if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getRHS())){   
	      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
                if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
		   //check if variable is initialized
		   if(VD->hasInit()){
		      if(APValue *APV = VD->evaluateValue()){
			const uint64_t *tmp_rank = APV->getInt().getRawData();
			rank = static_cast<int>(*tmp_rank);
		      
			return rank;
		      }
		   }else {
			return -2;
		   }
		}
	      }  
	    }
	  } 
	  
	  
	  return -1;
      }
      
      //check rankNames vector contain the given variable names
      bool isRankName(std::string varName)
      {
	  for(std::vector<std::string>::iterator it = rankNames.begin(); it != rankNames.end(); it++)
	  {
		   if(varName.compare(*it) == 0)
		   {
		      return true;
		   }
	  }
	  
	  return false;
      }
      
      
      //get rank
      int getRankNum(ImplicitCastExpr *ICE)
      {  
	  int rank;
	    
	  //get rank from a variable
	  if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
             if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
	       //check if variable is initialized
	       if(VD->hasInit()){
		  if(APValue *APV = VD->evaluateValue()){
		      const uint64_t *tmp_rank = APV->getInt().getRawData();
 		      rank = static_cast<int>(*tmp_rank);
		      
		      return rank;
		  }
	       }else {
		 return -2;
	       }
	     }
	  }
	  
	  //something went wrong
	  return -1;
      }
     
      
      //visit and update endpoint trees
      void visitTree(BinaryOperator *BO, Stmt *stmt ,  int rank)
      {
	    cur_rank = rank;
	    all_ranks = false;
	
	    //binary operators
	    std::string eq = "==";
	    std::string neq = "!=";
	    std::string ge = ">=";
	    std::string le = "<=";
	    std::string gre = ">";
	    std::string less = "<";
	    
	    
	    if (strcmp(BO->getOpcodeStr(), eq.c_str()) == 0)
	    {
		bin_op = eq;
		BaseStmtVisitor::Visit(stmt);
		
		all_ranks = true;
		
	    } else if(strcmp(BO->getOpcodeStr(), neq.c_str()) == 0)
	    {
	      bin_op = neq;
	      BaseStmtVisitor::Visit(stmt);
	      
	      all_ranks = true;
	      
	    } else if (strcmp(BO->getOpcodeStr(), ge.c_str()) == 0)
	    {
		bin_op = ge;	
		BaseStmtVisitor::Visit(stmt);
		
		all_ranks = true;
		
	    } else if (strcmp(BO->getOpcodeStr(), le.c_str()) == 0)
	    {
		bin_op = le;	
		BaseStmtVisitor::Visit(stmt);
		
		all_ranks = true;
		
	    } else if (strcmp(BO->getOpcodeStr(), gre.c_str()) == 0)
	    {
		bin_op = gre;	
		BaseStmtVisitor::Visit(stmt);
		
		all_ranks = true;
		
	    } else if (strcmp(BO->getOpcodeStr(), less.c_str()) == 0)
	    {
		bin_op = less;	
		BaseStmtVisitor::Visit(stmt);
		
		all_ranks = true;
	    }
      }
      
      
      //this method is used only by ELSE stmts
      void visitTree_elseStmt(Stmt *stmt, int rank)
      {
	//std::cout << "visitElseStmt " << rank << std::endl;
	  cur_rank = rank;
	  all_ranks = false;
	
	  //binary operators
	  std::string eq = "==";
	  
	  //assing binary operator
	  bin_op = eq;
	  BaseStmtVisitor::Visit(stmt);
		
	  all_ranks = true;
      }
      
      
     //update endpoint trees - eirther all or depending on the condition (of If Stmt, etc..)
     void updateTree(st_node *node, std::string src_or_dest, std::string tag, std::string mpi_datatype1, std::string mpi_datatype2)
      {
	 //binary operators
	 std::string eq = "==";
	 std::string neq = "!=";
	 std::string ge = ">=";
	 std::string le = "<=";
	 std::string gre = ">";
	 std::string less = "<";
	
         //counter for rank
	 int tmp_rank = 0;
	 
	 std::vector< std::stack<st_node*> >::iterator it1 = appendto_nodes.begin();
	 
	 if (all_ranks == true)
	 {	
	   //std::cout << "all ranks" << std::endl;
	   
	      std::list<int> tmp_listOfRanks;
	   
	      if(isIfStmt == true)
	      {
		if(stackOfRanks.top().empty())
		{
		  stackOfRanks.pop();
		}else{
		  tmp_listOfRanks = stackOfRanks.top();
		  stackOfRanks.pop();
		}
	      }
	   
	       int counter = 0;
	   
		while(it1 != appendto_nodes.end())
		{	
		  if(isCollectiveOper == true && collectiveOperRoot == counter)
		  {
		    st_node * previous_node = (*it1).top();
		    st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		  }else if (isCollectiveOper == true && collectiveOperRoot != counter){
		   //ignore
		  }else{
		   st_node * previous_node = (*it1).top();
		   st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		  }
		    
		   if(isIfStmt == true)
		   {
		      tmp_listOfRanks.push_back(counter);
		   }
		   
		   counter++;
		   it1++;
		}
		
		if(isIfStmt == true)
		{
		  tmp_listOfRanks.sort();
		  tmp_listOfRanks.unique();
		
		  stackRankOnLvlOfInd.push(tmp_listOfRanks);
		  stackOfRanks.push(tmp_listOfRanks);
		}

	 //if not all trees need update and IF stmt is not in indentation level greater or equal than 2 (leveling starts at level 1)
	 } else if(all_ranks == false && lvlOfIndent < 2)
	 { 
	   //std::cout << "<2" << std::endl;
	   
	   //every time that we are in the first IF stms we remove all lists of stack
	   while(stackRankOnLvlOfInd.size() >= 1)
	   {
	       stackRankOnLvlOfInd.pop();
	   }
	  
	   std::list<int> emptyList;
	   stackRankOnLvlOfInd.push(emptyList);
	   
	   //temporary (current) rank list
	   std::list<int> ranksList; 
	   
	   if(isEntryLvlElseStmt == false)
	   {
	     ranksList = stackOfRanks.top();
	     
	     //remove list from stack
	     stackOfRanks.pop();
	   }else{
	    stackOfRanks.pop();
	    
	    isEntryLvlElseStmt = false;
	   }
	   
	   
	   if(isEntryLvlElseIfStmt == true)
	   {
		isEntryLvlElseIfStmt = false;
	   }
	    
	    if (strcmp(bin_op.c_str(), eq.c_str()) == 0)
	    { 
		while(it1 != appendto_nodes.end())
		{	
		   if (tmp_rank == cur_rank)
		   { 
		      if(isCollectiveOper == true && collectiveOperRoot == tmp_rank)
		      {
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		      }else if(isCollectiveOper == true && collectiveOperRoot != tmp_rank){
			//ignore
		      }else {
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		      }
		      
		     
		      //put rank on list
		      ranksList.push_front(tmp_rank);
		      stackRankOnLvlOfInd.top().push_back(tmp_rank);
		   }
		   
		   
		   tmp_rank++;
		   it1++;
		} 
		
	    } else if(strcmp(bin_op.c_str(), neq.c_str()) == 0)
	    {
	      while(it1 != appendto_nodes.end())
		{	
		   if (tmp_rank != cur_rank)
		   { 
		     if(isCollectiveOper == true && collectiveOperRoot == tmp_rank)
		     {
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		     }else if(isCollectiveOper == true && collectiveOperRoot != tmp_rank){
			//ignore
		     }else{
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		     }
		      
		      //put rank on list
		      ranksList.push_front(tmp_rank);
		      stackRankOnLvlOfInd.top().push_back(tmp_rank);
		   }
		   
		   
		   tmp_rank++;
		   it1++;
		}
	
	    } else if (strcmp(bin_op.c_str(), ge.c_str()) == 0)
	    { 
		while(it1 != appendto_nodes.end())
		{	
		  if(tmp_rank >= cur_rank)
		  {
		    if(isCollectiveOper == true && collectiveOperRoot == tmp_rank)
		    {
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		    }else if(isCollectiveOper == true && collectiveOperRoot != tmp_rank){
			//ignore
		    }else{
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		    } 
		    
		    //put rank(s) on list
		    ranksList.push_front(tmp_rank);
		    stackRankOnLvlOfInd.top().push_back(tmp_rank);
		  }
		  
		   tmp_rank++;
		   it1++;
		}    
	      
	    } else if (strcmp(bin_op.c_str(), le.c_str()) == 0)
	    {
		while(it1 != appendto_nodes.end())
		{	
		  if(tmp_rank <= cur_rank)
		  {
		    if(isCollectiveOper == true && collectiveOperRoot == tmp_rank)
		    {
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		    }else if(isCollectiveOper == true && collectiveOperRoot != tmp_rank){
			//ignore
		    }else{
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		    }
		    
		    //put rank(s) on list
		    ranksList.push_front(tmp_rank);
		    stackRankOnLvlOfInd.top().push_back(tmp_rank);
		  }
		  
		   tmp_rank++;
		   it1++;
		}  
		
	    } else if (strcmp(bin_op.c_str(), gre.c_str()) == 0)
	    {
		
	      while(it1 != appendto_nodes.end())
		{	
		  if(tmp_rank > cur_rank)
		  {
		    if(isCollectiveOper == true && collectiveOperRoot == tmp_rank)
		    {
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		    }else if(isCollectiveOper == true && collectiveOperRoot != tmp_rank){
			//ignore
		    }else{
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		    }
		    
		    //put rank(s) on list
		    ranksList.push_front(tmp_rank);
		    stackRankOnLvlOfInd.top().push_back(tmp_rank);
		  }
		    
		   tmp_rank++;
		   it1++;
		}  
	      
	    } else if (strcmp(bin_op.c_str(), less.c_str()) == 0)
	    {
		while(it1 != appendto_nodes.end())
		{	
		  if(tmp_rank < cur_rank)
		  {
		    if(isCollectiveOper == true && collectiveOperRoot == tmp_rank)
		    {
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		    }else if(isCollectiveOper == true && collectiveOperRoot != tmp_rank){
			//ignore
		    }else{
			st_node * previous_node = (*it1).top();
			st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		    }
		    
		    //put rank(s) on list
		    ranksList.push_front(tmp_rank);
		    stackRankOnLvlOfInd.top().push_back(tmp_rank);
		  }
		  
		   tmp_rank++;
		   it1++;
		}   
	    } 
	    
	    //sort list - in order to remove duplicates
	    ranksList.sort();
	    //remove duplicates
	    ranksList.unique();
	    //push list on the stackisInStack(*it_l, stackOfRanks, true) && 
	    stackOfRanks.push(ranksList);
	    
// 	    for(std::list<int>::iterator it_l = ranksList.begin(); it_l != ranksList.end(); it_l++)
// 	    {
// 	      std::cout << "bottomlist <2: " << *it_l << std::endl;
// 	    }
	    
	     
	   // level of identation in the IF stmt is equal or greater than 2
	   //put ranks in bottom list which will be the ranks of inner IF stmt
	 } else if(all_ranks == false && lvlOfIndent >= 2)
	 { 
	   //std::cout << ">=2: " << lvlOfIndent << std::endl;
	   
	   while(stackRankOnLvlOfInd.size() >= lvlOfIndent)
	   {
	     stackRankOnLvlOfInd.pop();
	   }
	   
	   std::list<int> emptyList;
	   stackRankOnLvlOfInd.push(emptyList);
	   
	   //list of parent IF statement
	    std::list<int> topList;
	    //list of indent IF statement
	    std::list<int> bottomList;
	    
	    //the list that will contain the trees that are allowed to be updated
	    //due to the indented IF not all trees can be update since we have the outer IF stmt
	    std::list<int> ranksList;

	    std::list<int> tmp_bottomLIst;
	   
	   //top list is empty only when in the first call (of each "rank" - NOT generally of the whole IF) of parent IF
	   //that is because each "rank" in parent IF, on the first call ONLY will put an empty list on stack
	   //so each time we need to remove it and use previous one
	   if(stackOfRanks.top().empty())
	   {
	     stackOfRanks.pop();
	     
	     if(isEntryLvlElseIfStmt == true)
	     {
	       stackOfRanks.pop();
	       topList = stackOfRanks.top();
	       isEntryLvlElseIfStmt = false;
	     }else{
	       
		topList = stackOfRanks.top();
	     }
	     
	   }else{
	     
	     if(isEntryLvlElseStmt == false)
	     {
		bottomList = stackOfRanks.top();
		tmp_bottomLIst = bottomList;
	     }else{
	        isEntryLvlElseStmt = false; 
	     }
	     
	     stackOfRanks.pop();
	     topList = stackOfRanks.top();
	   }
	   
// 	   for(std::list<int>::iterator it_l = bottomList.begin(); it_l != bottomList.end(); it_l++)
// 	    {
// 	      std::cout << "bottomlist >=2 before : " << *it_l << std::endl;
// 	    }
// 	    
// 	    for(std::list<int>::iterator it_l = topList.begin(); it_l != topList.end(); it_l++)
// 	    {
// 	      std::cout << "toplist >=2 before : " << *it_l << std::endl;
// 	    }
	   
	   
	    //loop counter
	    int counter = 0;
	    
	    if (strcmp(bin_op.c_str(), eq.c_str()) == 0)
	    { 
		while(counter < num_of_processors)
		{	
		   if (tmp_rank == cur_rank)
		   {  //put rank on list
		      bottomList.push_front(tmp_rank);
		      stackRankOnLvlOfInd.top().push_back(tmp_rank);
		   }
		   
		   tmp_rank++;
		   counter++;
		} 
		
	    } else if(strcmp(bin_op.c_str(), neq.c_str()) == 0)
	    {
	      while(counter < num_of_processors)
		{	
		   if (tmp_rank != cur_rank)
		   {  //put rank on list
		      bottomList.push_front(tmp_rank);
		      stackRankOnLvlOfInd.top().push_back(tmp_rank);
		   }
		   
		   tmp_rank++;
		   counter++;
		}
	
	    } else if (strcmp(bin_op.c_str(), ge.c_str()) == 0)
	    { 
		while(counter < num_of_processors)
		{	
		  if(tmp_rank >= cur_rank)
		  { //put rank(s) on list
		    bottomList.push_front(tmp_rank);
		    stackRankOnLvlOfInd.top().push_back(tmp_rank);
		  }
		  
		   tmp_rank++;
		   counter++;
		}    
	      
	    } else if (strcmp(bin_op.c_str(), le.c_str()) == 0)
	    {
		while(counter < num_of_processors)
		{	
		  if(tmp_rank <= cur_rank)
		  { //put rank(s) on list
		    bottomList.push_front(tmp_rank);
		    stackRankOnLvlOfInd.top().push_back(tmp_rank);
		  }
		  
		   tmp_rank++;
		   counter++;
		}  
		
	    } else if (strcmp(bin_op.c_str(), gre.c_str()) == 0)
	    {
		
	      while(counter < num_of_processors)
		{	
		  if(tmp_rank > cur_rank)
		  { //put rank(s) on list
		    bottomList.push_front(tmp_rank);
		    stackRankOnLvlOfInd.top().push_back(tmp_rank);
		  }
		    
		   tmp_rank++;
		   counter++;
		}  
	      
	    } else if (strcmp(bin_op.c_str(), less.c_str()) == 0)
	    {
		while(counter < num_of_processors)
		{	
		  if(tmp_rank < cur_rank)
		  {//put rank(s) on list
		    bottomList.push_front(tmp_rank);
		    stackRankOnLvlOfInd.top().push_back(tmp_rank);
		  }
		  
		   tmp_rank++;
		   counter++;
		}   
	    }
	    
	    //toplist is empty ONLY if parent IF updated "all ranks" (all_ranks == true)
	    //so we need to fill it with all ranks
	    if(topList.empty())
	    {
	      for(int i = 0; i < num_of_processors; i++)
	      {
		topList.push_back(i);
	      }
	    }
	    
	    //generate the rank list
	    ranksList = checkLists(topList, bottomList);
	    
	    //sort list
	    ranksList.sort();
	    //remove duplicates from list
	    ranksList.unique();
	    
	    bottomList.sort();
	    bottomList.unique();
	    //push list on the stack
	    stackOfRanks.push(bottomList);
	    
	    tmp_bottomLIst.sort();
	    tmp_bottomLIst.unique();
	    
	    //if list is empty it means we can update all ranks in ranks list
	    if(tmp_bottomLIst.empty())
	    {	    
		for(std::list<int>::iterator it_l = ranksList.begin(); it_l != ranksList.end(); it_l++)
		{
		  //if rank is in all the lists of stack - each list shows the ranks of each level of the current call
		  if(isInStack(*it_l, stackRankOnLvlOfInd, true))
		  {
		    cur_rank = *it_l;
		    updateTree_indentIf(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2);
		  }
		}
	    }else{
	      for(std::list<int>::iterator it_l = ranksList.begin(); it_l != ranksList.end(); it_l++)
	      {
		//if tree has not already updated and rank is in all list of stack
		if(isInList(tmp_bottomLIst, *it_l) == 2 && isInStack(*it_l, stackRankOnLvlOfInd, true))
		{
		  cur_rank = *it_l;
		  updateTree_indentIf(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2);
		}
	      }
	    }
	    
// 	     for(std::list<int>::iterator it_l = bottomList.begin(); it_l != bottomList.end(); it_l++)
// 	    {
// 	      std::cout << "bottomlist >=2 after : " << *it_l << std::endl;
// 	    }
	     
	 }
      }
      
      //this update tree is used only for IF stmts that are indented
      void updateTree_indentIf(st_node *node, std::string src_or_dest, std::string tag, std::string mpi_datatype1, std::string mpi_datatype2)
      { 
         //counter for rank
	 int tmp_rank = 0;
	 
	 std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	   
	 while(it != appendto_nodes.end())
	 {	
	     if (tmp_rank == cur_rank)
	     { 
	       if(isCollectiveOper == true && collectiveOperRoot == tmp_rank)
	       {
		    st_node * previous_node = (*it).top();
		    st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		}else if(isCollectiveOper == true && collectiveOperRoot != tmp_rank){
			//ignore
		}else{
	            st_node * previous_node = (*it).top();
	            st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
		}
	     }
		     
	     tmp_rank++;
	     it++;
	} 
      }
      
      
      //this update tree is used only for not IF stmts and collective operators (Bcast and Reduce)
      void updateTree_collectiveOper(st_node *node, std::string src_or_dest, std::string tag, std::string mpi_datatype1, std::string mpi_datatype2)
      { 
         //counter for rank
	 int tmp_rank = 0;
	 
	 std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	   
	 while(it != appendto_nodes.end())
	 {	
	     if (tmp_rank == collectiveOperRoot)
	     { 
		 st_node * previous_node = (*it).top();
		 st_node_append(previous_node, createNode(node, src_or_dest, tag, mpi_datatype1, mpi_datatype2));
	     }
		     
	     tmp_rank++;
	     it++;
	} 
      }
 
      
      //create a node
      st_node* createNode(const st_node *tmp_node, std::string src_or_dest, std::string tag, std::string mpi_datatype1, std::string mpi_datatype2){
	 
	 st_node *node;
	 std::string hyphen_tag = "-";
	 
	 switch (tmp_node->type) {
            
	    case ST_NODE_SEND: // ---------- SEND ----------
		node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_SEND);
                node->interaction->from = NULL;
		
                node->interaction->nto = 1;
                node->interaction->to = (char **)calloc(sizeof(char *), node->interaction->nto);
                node->interaction->to[0] = (char *)calloc(sizeof(char), src_or_dest.size()+1);
                strcpy(node->interaction->to[0], src_or_dest.c_str());
                if (tag.compare("") == 0) {
                  node->interaction->msgsig.op = NULL;
                } else {
                  node->interaction->msgsig.op = (char *)calloc(sizeof(char), tag.size()+1);
                  strcpy(node->interaction->msgsig.op, tag.c_str());
                }
                node->interaction->msgsig.payload = (char *)calloc(sizeof(char), mpi_datatype1.size()+1);
                strcpy(node->interaction->msgsig.payload, mpi_datatype1.c_str());
		return node;
		break;
		
	    case ST_NODE_ISEND: // ---------- ISEND ----------
		node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_ISEND);
                node->interaction->from = NULL;
                node->interaction->nto = 1;
                node->interaction->to = (char **)calloc(sizeof(char *), node->interaction->nto);
                node->interaction->to[0] = (char *)calloc(sizeof(char), src_or_dest.size()+1);
                strcpy(node->interaction->to[0], src_or_dest.c_str());
                if (tag.compare("") == 0) {
                  node->interaction->msgsig.op = NULL;
                } else {
                  node->interaction->msgsig.op = (char *)calloc(sizeof(char), tag.size()+1);
                  strcpy(node->interaction->msgsig.op, tag.c_str());
                }
                node->interaction->msgsig.payload = (char *)calloc(sizeof(char), mpi_datatype1.size()+1);
                strcpy(node->interaction->msgsig.payload, mpi_datatype1.c_str());
		return node;
		break;
		
	    case ST_NODE_RECV: // ----------- RECV -----------
		node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_RECV);
                node->interaction->from = (char *)calloc(sizeof(char), src_or_dest.size()+1);
		 strcpy(node->interaction->from, src_or_dest.c_str());
                node->interaction->nto = 0;
                node->interaction->to = NULL;
        
                if (tag.compare("") == 0) {
                  node->interaction->msgsig.op = NULL;
                } else {
                  node->interaction->msgsig.op = (char *)calloc(sizeof(char), tag.size()+1);
                  strcpy(node->interaction->msgsig.op, tag.c_str());
                }
                node->interaction->msgsig.payload = (char *)calloc(sizeof(char), mpi_datatype1.size()+1);
                strcpy(node->interaction->msgsig.payload, mpi_datatype1.c_str());
		return node;
	        break;
	    
            case ST_NODE_IRECV: // ----------- IRECV -----------
		node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_IRECV);
                node->interaction->from = (char *)calloc(sizeof(char), src_or_dest.size()+1);
		 strcpy(node->interaction->from, src_or_dest.c_str());
                node->interaction->nto = 0;
                node->interaction->to = NULL;
        
                if (tag.compare("") == 0) {
                  node->interaction->msgsig.op = NULL;
                } else {
                  node->interaction->msgsig.op = (char *)calloc(sizeof(char), tag.size()+1);
                  strcpy(node->interaction->msgsig.op, tag.c_str());
                }
                node->interaction->msgsig.payload = (char *)calloc(sizeof(char), mpi_datatype1.size()+1);
                strcpy(node->interaction->msgsig.payload, mpi_datatype1.c_str());
		return node;
		break;
	   
	    case ST_NODE_BCAST: // ---------- BCAST ----------
		 node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_BCAST);
                node->interaction->from = (char *)calloc(sizeof(char), src_or_dest.size()+1);
		 strcpy(node->interaction->from, src_or_dest.c_str());
              
		 node->interaction->nto = 1;
                node->interaction->to = (char **)calloc(sizeof(char *), node->interaction->nto);
		src_or_dest.clear();
		src_or_dest = "Others";
                node->interaction->to[0] = (char *)calloc(sizeof(char), src_or_dest.size()+1);
		strcpy(node->interaction->to[0], src_or_dest.c_str());
		 
                node->interaction->msgsig.op = NULL;
                node->interaction->msgsig.payload = (char *)calloc(sizeof(char), mpi_datatype1.size()+1);
                strcpy(node->interaction->msgsig.payload, mpi_datatype1.c_str());
		return node;
	        break;

            case ST_NODE_REDUCE: // ---------- REDUCE ----------
		node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_REDUCE);
                node->interaction->from = NULL;
                node->interaction->nto = 1;
                node->interaction->to = (char **)calloc(sizeof(char *), node->interaction->nto);
                node->interaction->to[0] = (char *)calloc(sizeof(char), src_or_dest.size()+1);
                strcpy(node->interaction->to[0], src_or_dest.c_str());
		
		src_or_dest.clear();
		src_or_dest = "Others";
		node->interaction->from = (char *)calloc(sizeof(char), src_or_dest.size()+1);
		strcpy(node->interaction->from, src_or_dest.c_str());
		
                node->interaction->msgsig.op = NULL;
                node->interaction->msgsig.payload = (char *)calloc(sizeof(char), mpi_datatype1.size()+1);
                strcpy(node->interaction->msgsig.payload, mpi_datatype1.c_str());
		return node;
                break;
      }
    }

      
   /*binary operator "&&" or "||" has in both sides a "rank" variable*/
   bool hasTwoRanks(BinaryOperator *BO)
   {
       std::string and_bin = "&&";
       std::string or_bin = "||";
       
       bool hasRankLHS = false;
       bool hasRankRHS = false;

       
	    if (strcmp(BO->getOpcodeStr(), and_bin.c_str()) == 0 || strcmp(BO->getOpcodeStr(), or_bin.c_str()) == 0){
	      
		// if rank is in LHS make boolean true
		if(isa<BinaryOperator>(BO->getLHS())){   
	          if(BinaryOperator *tmp_BO = dyn_cast<BinaryOperator>(BO->getLHS())){  
		     if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(tmp_BO->getLHS())){
		        if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			   if(VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			      if(isRankName(VD->getNameAsString())){
				  hasRankLHS = true;
			      }
			   }
			}
		      }
		    }
		}
	    
		// if rank is in RHS make boolean true
		if(isa<BinaryOperator>(BO->getRHS())){
	          if(BinaryOperator *tmp_BO = dyn_cast<BinaryOperator>(BO->getRHS())){  
		     if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(tmp_BO->getLHS())){
		        if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			   if(VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			      if(isRankName(VD->getNameAsString())){
				  hasRankRHS = true;
			      }
			   }
			}
		      }
		    }
		}
	    }
	    
	    //if both sides of binary operator have "rank" then return (ignore if statement)
	    if (hasRankLHS == true && hasRankRHS == true)
	    {
	        return true;
		
	    } else 
	    {
		return false; 
	    }
   }
   
   
   //binary operator "&&" or "||" has ONLY on one side a "rank" variable (returns false if 2 "ranks" or 0 "ranks")
   //other binary operators have a "rank" variable 
   bool hasOneRank(BinaryOperator *BO)
   {
       //binary operators
       std::string eq = "==";
       std::string neq = "!=";
       std::string ge = ">=";
       std::string le = "<=";
       std::string gre = ">";
       std::string less = "<";
       std::string and_bin = "&&";
       std::string or_bin = "||";
       
       bool hasRankLHS = false;
       bool hasRankRHS = false;
       bool hasRankOtherBinOp = false;

	    
	    if (strcmp(BO->getOpcodeStr(), and_bin.c_str()) == 0 || strcmp(BO->getOpcodeStr(), or_bin.c_str()) == 0){
	      
		// if rank is in LHS make boolean true
		if(isa<BinaryOperator>(BO->getLHS())){   
	          if(BinaryOperator *tmp_BO = dyn_cast<BinaryOperator>(BO->getLHS())){  
		     if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(tmp_BO->getLHS())){
		        if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			   if(VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			      if(isRankName(VD->getNameAsString())){
				  hasRankLHS = true;
			      }
			   }
			}
		      }
		    }
		}
	    
		// if rank is in RHS make boolean true
		if(isa<BinaryOperator>(BO->getRHS())){
	          if(BinaryOperator *tmp_BO = dyn_cast<BinaryOperator>(BO->getRHS())){  
		     if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(tmp_BO->getLHS())){
		        if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			   if(VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			      if(isRankName(VD->getNameAsString())){
				  hasRankRHS = true;
			      }
			   }
			}
		      }
		    }
		}
	    }
	    
	    //check if other binary operator except && or || have a "rank" variable
	    if (strcmp(BO->getOpcodeStr(), eq.c_str()) == 0 || strcmp(BO->getOpcodeStr(), neq.c_str()) == 0 
	            || strcmp(BO->getOpcodeStr(), ge.c_str()) == 0 || strcmp(BO->getOpcodeStr(), le.c_str()) == 0
		    || strcmp(BO->getOpcodeStr(), gre.c_str()) == 0 || strcmp(BO->getOpcodeStr(), less.c_str()) == 0)
	    {
		if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getLHS())){
		    if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
		      if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			    if(isRankName(VD->getNameAsString())){
			       hasRankOtherBinOp = true;
			    }
			}
		    }
		}
	    }
	    
	    //if in other bin op (except && and ||) there is a "rank" variable
	    if(hasRankOtherBinOp == true)
	    {
	      return true;
	    }
	    
	    
	    //if only one side has a rank variable
	    if((hasRankLHS == true && hasRankRHS == false) || (hasRankLHS == false && hasRankRHS == true))
	    {
	      return true;
	    }else{
	      
	      return false;
	    }
   }
      
      
   //visit all binary operators   
   void visitAllOtherBinOps(BinaryOperator *BO, Stmt *stmt, bool callFromIFStmt, std::vector<st_node*> choice_nodes)
   {   
       std::string neq = "!=";
       std::string and_bin = "&&";
       std::string or_bin = "||";
       
       //parenthesis is on LHS, RHS or both in Binary Operator
       bool isLHSParen = false;
       bool isRHSParen = false;
       
       //check if binary operator is && (AND)
       if(isa<BinaryOperator>(BO) && strcmp(BO->getOpcodeStr(), and_bin.c_str()) == 0)
       {
	  //check if there is parenthesis in binary operator
	  if(isa<ParenExpr>(BO->getLHS()) || isa<ParenExpr>(BO->getRHS()))
	  {
	    //check if parenthesis on LHS
	    if(isa<ParenExpr>(BO->getLHS()))
	    {
	      if(ParenExpr *PE = dyn_cast<ParenExpr>(BO->getLHS())){
		if(BinaryOperator *Par_BO = dyn_cast<BinaryOperator>(PE->getSubExpr())){
		  if(BinaryOperator *BO_RHS = dyn_cast<BinaryOperator>(BO->getRHS())){
		    // if both parenthesis (and both side of parenthesis operator) and the non-parenthesis side have "rank" then ignore
		    if(hasTwoRanks(Par_BO) == true  && hasOneRank(BO_RHS) == true){
			return;
			
		     // if ((rank && int) && rank)
		    }else if (hasOneRank(Par_BO) == true && hasOneRank(BO_RHS) == true && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0){
		      
		      return;
		      
		     //if ((int && int) && rank) - new
		    }else if(hasOneRank(Par_BO) == false  && hasOneRank(BO_RHS) == true && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0){
		        
			isLHSParen = true;
			
			if(callFromIFStmt == true)
			{
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			}
			
			//if ((int && rank) && int) - one side of parenthesis has rank 
		    }else if(hasOneRank(Par_BO) == true  && hasOneRank(BO_RHS) == false && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0){
		       
			isLHSParen = true;
			
			callFromIFStmt = false;
			
			visitAllOtherBinOps(Par_BO, stmt, false, choice_nodes);
		      
		     // if ((rank || int) && rank)
		    }else if (hasOneRank(Par_BO) == true && hasOneRank(BO_RHS) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0){
		         
		      //YES
		      isLHSParen = true;
		      
		      if(callFromIFStmt == true)
		      {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
		      }
		       
		     //if (rank && (int || int))
		    }else if (hasOneRank(Par_BO) == false && hasOneRank(BO_RHS) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0){
			 
		      
		      isLHSParen = true;
		      
		      if(callFromIFStmt == true)
		      {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
		      }
		      
		      //if((rank || rank)&& int)
		    }else if (hasOneRank(BO_RHS) == false && hasTwoRanks(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0){
		      
		      isLHSParen = true;
		      
		      if(callFromIFStmt == true)
		      {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
		      }
		      
		      visitAllOtherBinOps(Par_BO, stmt, false, choice_nodes);
		     
		     //if ((int || int) && int) or if ((int && int) && int)
		    }else if (hasOneRank(BO_RHS) == false && hasOneRank(Par_BO) == false){
		      
		      if(callFromIFStmt == true)
		      {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
		      }
		      
		      BaseStmtVisitor::Visit(stmt);
		      return;
			
		    //if((int || rank)&& int)
		    }else if (hasOneRank(BO_RHS) == false && hasOneRank(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0){
		      
		      if(callFromIFStmt == true)
		      {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
		      }
		      
		      BaseStmtVisitor::Visit(stmt);
			return;
		    
		    }else { //no ranks at all
		        llvm::errs() << "\nNot known condition - IF Stmt\n";
			BO->dump();
			return; 
		    }
		  }
		}
	      }
	    }
	  
	    //check if parenthesis on RHS
	    if(isa<ParenExpr>(BO->getRHS()))
	    {
	      if(ParenExpr *PE = dyn_cast<ParenExpr>(BO->getRHS())){
		if(BinaryOperator *Par_BO = dyn_cast<BinaryOperator>(PE->getSubExpr())){
		   if(BinaryOperator *BO_LHS = dyn_cast<BinaryOperator>(BO->getLHS())){
		      // if both parenthesis (both sides of operator) and the non-parenthesis side have "rank" then ignore 
		      if(hasTwoRanks(Par_BO) == true && hasOneRank(BO_LHS) == true){
			
			return;
			  
			// if (rank && (rank && int))
		      } else if (hasOneRank(Par_BO) == true && hasOneRank(BO_LHS) == true && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0){
			
			return;
			
		     //if (rank && (int && int)) or (rank && (int || int))
		    }else if(hasOneRank(Par_BO) == false  && hasOneRank(BO_LHS) == true){
		        
			isRHSParen = true;
			
			if(callFromIFStmt == true)
			{
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			}
			
		     //if (int && (int && rank)) - one side of parenthesis has rank
		    }else if(hasOneRank(Par_BO) == true  && hasOneRank(BO_LHS) == false && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0){
		        
			isRHSParen = true;
			
			callFromIFStmt = false;
			
			visitAllOtherBinOps(Par_BO, stmt, false, choice_nodes);
			
		       // if (rank && (rank || int))
		      }else if (hasOneRank(Par_BO) == true && hasOneRank(BO_LHS) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0){
		        
			isRHSParen = true;
			
			if(callFromIFStmt == true)
			{
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			}
		      
		       //if (rank && (int || int))
		      }else if (hasOneRank(Par_BO) == false && hasOneRank(BO_LHS) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0){
			
			isRHSParen = true;
			
			if(callFromIFStmt == true)
			{
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			}
			
			//if(int && (rank || rank))
		      }else if (hasOneRank(BO_LHS) == false && hasTwoRanks(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0){
			
			isRHSParen = true;
			
			if(callFromIFStmt == true)
			{
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			}
			
			visitAllOtherBinOps(Par_BO, stmt, false, choice_nodes);
		 
		      //if ((int || int) && int) or ((int && int) && int)
		      }else if (hasOneRank(BO_LHS) == false && hasOneRank(Par_BO) == false && hasTwoRanks(BO_LHS) == false){
			
			if(callFromIFStmt == true)
			{
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			}
			
			BaseStmtVisitor::Visit(stmt);
			return;
			
		      //if(int && (int || rank))
		      }else if (hasOneRank(BO_LHS) == false && hasOneRank(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0){
			
			if(callFromIFStmt == true)
			{
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			}
			
			BaseStmtVisitor::Visit(stmt);
			return;
		    
		      }else { //no ranks at all
		        llvm::errs() << "\nNot known condition - IF Stmt\n";
			BO->dump();
			return; 
		      }
		    }
		}
	      }
	    }
	  }
       }
       
       
       //check if binary operator is || (OR)
       if(isa<BinaryOperator>(BO) && strcmp(BO->getOpcodeStr(), or_bin.c_str()) == 0)
       {   
	  //check if there is parenthesis in binary operator
	  if(isa<ParenExpr>(BO->getLHS()) || isa<ParenExpr>(BO->getRHS()))
	  {
	    //check if parenthesis on LHS
	    if(isa<ParenExpr>(BO->getLHS()))
	    {
	      if(ParenExpr *PE = dyn_cast<ParenExpr>(BO->getLHS())){
		if(BinaryOperator *Par_BO = dyn_cast<BinaryOperator>(PE->getSubExpr())){
		  if(BinaryOperator *BO_RHS = dyn_cast<BinaryOperator>(BO->getRHS())){
		    if(BinaryOperator *ParBO_RHS = dyn_cast<BinaryOperator>(Par_BO ->getRHS())){
		      if(BinaryOperator *ParBO_LHS = dyn_cast<BinaryOperator>(Par_BO ->getLHS())){
			//if ((rank != int x || rank != int y) || rank != int z) - both sides of parenthesis have rank and non parenthesis side - x, y or z not same
			if(hasTwoRanks(Par_BO) == true && hasOneRank(BO_RHS) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0
			  && strcmp(BO_RHS->getOpcodeStr(), neq.c_str()) == 0 && (strcmp(ParBO_RHS->getOpcodeStr(), neq.c_str()) == 0
			  && strcmp(ParBO_LHS->getOpcodeStr(), neq.c_str()) == 0)){
			 
			  BaseStmtVisitor::Visit(stmt);
			  return;
			  
			}
			//if ((rank != int || int) || rank != int) -any side of parenthesis can be rank and also non-parenthesis side is rank
		        else if(hasOneRank(Par_BO) == true && hasOneRank(BO_RHS) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0
			  && strcmp(BO_RHS->getOpcodeStr(), neq.c_str()) == 0 && (strcmp(ParBO_RHS->getOpcodeStr(), neq.c_str()) == 0
			  || strcmp(ParBO_LHS->getOpcodeStr(), neq.c_str()) == 0)){
			  
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
			
			//if ((rank !=  || rank != ) || int) - both side of parenthesis have rank but non parenthesis side - new
			}else if(hasTwoRanks(Par_BO) == true && hasOneRank(BO_RHS) == false && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0
			  && (strcmp(ParBO_RHS->getOpcodeStr(), neq.c_str()) == 0 && strcmp(ParBO_LHS->getOpcodeStr(), neq.c_str()) == 0)){
			 
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
			  
			 //if ((int || rank ) || int) - any side of parenthesis but non parenthesis side 
			}else if(hasOneRank(Par_BO) == true && hasOneRank(BO_RHS) == false && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0)
			{
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
			  
		        // if ((rank || rank) || rank)
			}else if(hasTwoRanks(Par_BO) == true && hasOneRank(BO_RHS) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0){
			  //make bool true so the code below in this function 
			  //does NOT visit the LHS of binary operator 
			  isLHSParen = true;
			   
			  visitAllOtherBinOps(Par_BO, stmt, false, choice_nodes);
			  
			  callFromIFStmt = false;
			  
			//if ((rank && rank)|| rank)
			}else if(hasTwoRanks(Par_BO) == true && hasOneRank(BO_RHS) == true && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0){
			  isLHSParen = true;
			  
			  callFromIFStmt = false;
			  
			//if ((rank && int) || rank)
			}else if (hasOneRank(BO_RHS) == true && hasOneRank(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0)
			{
			  //make bool true so the code below in this function 
			  //does NOT visit the RHS of binary operator -- the call below will take care of the parenthesis
			  isLHSParen = true;
			  
			  callFromIFStmt = false;
			  
			  //visit binary operator that is inside the parenthesis
			  visitAllOtherBinOps(Par_BO, stmt, false, choice_nodes);
			
			//if ((rank || int) || rank)
			}else if (hasOneRank(BO_RHS) == true && hasOneRank(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0)
			{
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return; 
			
			//if ((rank || rank) || int)
			}else if (hasOneRank(BO_RHS) == false && hasTwoRanks(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0)
			{
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
			  
			//if ((int || int) || rank) or ((int && int) || rank)
			}else if (hasOneRank(Par_BO) == false && hasOneRank(BO_RHS) == true)
			{
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
			  
			//if ((rank && rank) || int)
			}else if(hasOneRank(BO_RHS) == false && hasTwoRanks(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0){
			  
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
			  
		        //if ((int && int) || int) or (int || int) || int)
			}else if (hasOneRank(BO_RHS) == false && hasOneRank(Par_BO) == false){ 
			  
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
		      
			//if((int && rank) || int)
			}else if(hasOneRank(BO_RHS) == false && hasOneRank(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0){
			  
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
		       
			}else{
			  llvm::errs() << "\nNot known condition - IF Stmt\n";
			  BO->dump();
			  return;  
			}
		      }
		    }
		  }
		}
	      }
	    }
	  
	    //check if parenthesis on RHS
	    if(isa<ParenExpr>(BO->getRHS()))
	    {
	      if(ParenExpr *PE = dyn_cast<ParenExpr>(BO->getRHS())){
		if(BinaryOperator *Par_BO = dyn_cast<BinaryOperator>(PE->getSubExpr())){
		  if(BinaryOperator *BO_LHS = dyn_cast<BinaryOperator>(BO->getLHS())){
		    if(BinaryOperator *ParBO_RHS = dyn_cast<BinaryOperator>(Par_BO ->getRHS())){
		      if(BinaryOperator *ParBO_LHS = dyn_cast<BinaryOperator>(Par_BO ->getLHS())){
			//if (rank != int x || (rank != int y || rank != int z)) - both sides of parenthesis have rank and non parenthesis side - x, y or z not same
			if(hasTwoRanks(Par_BO) == true && hasOneRank(BO_LHS) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0
			  && strcmp(BO_LHS->getOpcodeStr(), neq.c_str()) == 0 && (strcmp(ParBO_RHS->getOpcodeStr(), neq.c_str()) == 0
			  && strcmp(ParBO_LHS->getOpcodeStr(), neq.c_str()) == 0)){
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
			  
			 //if (rank != int || (rank != int || int)) -any side of parenthesis can be rank (or both)
			}else if(hasOneRank(Par_BO) == true && hasOneRank(BO_LHS) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0
			  && strcmp(BO_LHS->getOpcodeStr(), neq.c_str()) == 0 && (strcmp(ParBO_RHS->getOpcodeStr(), neq.c_str()) == 0
			  || strcmp(ParBO_LHS->getOpcodeStr(), neq.c_str()) == 0)){
			  
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
			
			//if (int || (rank !=  || rank != )) - both side of parenthesis have rank but non parenthesis side - new
			}else if(hasTwoRanks(Par_BO) == true && hasOneRank(BO_LHS) == false && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0
			  && (strcmp(ParBO_RHS->getOpcodeStr(), neq.c_str()) == 0 && strcmp(ParBO_LHS->getOpcodeStr(), neq.c_str()) == 0)){
			  
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
			
			//if (int || (int || rank))
			}else if(hasOneRank(Par_BO) == true && hasOneRank(BO_LHS) == false && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0)
			{
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
		        
			  //if (rank || (rank || rank))
			} else if(hasTwoRanks(Par_BO) == true && hasOneRank(BO_LHS) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0){
			  //make bool true so the code below in this function 
			  //does NOT visit the RHS of binary operator 
			  isRHSParen = true;
			  visitAllOtherBinOps(Par_BO, stmt, false, choice_nodes);
			  
			  callFromIFStmt = false;
		    
		          //if (rank || (rank && rank))
		        }else if(hasTwoRanks(Par_BO) == true && hasOneRank(BO_LHS) == true && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0){
			  isRHSParen = true;
			  
			  callFromIFStmt = false;
		      
		         //if (rank || (rank && int))
		        }else if (hasOneRank(BO_LHS) == true && hasOneRank(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0)
		        {
			  //make bool true so the code below in this function 
			  //does NOT visit the RHS of binary operator -- the call below will take care of the parenthesis
		 	  isRHSParen = true;
			  
			  callFromIFStmt = false;
		      
			  //visit binary operator that is inside the parenthesis
			  visitAllOtherBinOps(Par_BO, stmt, false, choice_nodes);
			
		        //if (rank || (rank || int))
		        }else if (hasOneRank(BO_LHS) == true && hasOneRank(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0)
		        {
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return; 
			  
			//if (int || (rank || rank))
			}else if (hasOneRank(BO_LHS) == false && hasTwoRanks(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0)
			{
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return; 
			  
			//if (rank || (int || int)) or (rank || (int && int))
			}else if (hasOneRank(Par_BO) == false && hasOneRank(BO_LHS) == true && strcmp(Par_BO->getOpcodeStr(), or_bin.c_str()) == 0)
			{
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
			  
			  //if (int || (rank && rank) )
		        }else if(hasOneRank(BO_LHS) == false && hasTwoRanks(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0){
		         if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
		      
		        //if (int || (int && int)) or (int || (int || int)) 
		        }else if (hasOneRank(BO_LHS) == false && hasOneRank(Par_BO) == false){ 
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
		    
		       //if(int || (int && rank))
		        }else if(hasOneRank(BO_LHS) == false && hasOneRank(Par_BO) == true && strcmp(Par_BO->getOpcodeStr(), and_bin.c_str()) == 0){
			  if(callFromIFStmt == true)
			  {
			    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
			    callFromIFStmt = false;
			  }
			  
			  BaseStmtVisitor::Visit(stmt);
			  return;
		     
		        }else{
			  llvm::errs() << "\nNot known condition - IF Stmt\n";
			  BO->dump();
			  return; 
		        }
		      }
		    }
		  }
	        }
	      }
	    }
	  }
       }
       
       //check if both sides of binary operator "&&" have "rank"
       if (hasTwoRanks(BO) == true && strcmp(BO->getOpcodeStr(), and_bin.c_str()) == 0)
       {
	  return;
       //rank || int
       }else if (hasOneRank(BO) == true && strcmp(BO->getOpcodeStr(), or_bin.c_str()) == 0)
       {
	  if(callFromIFStmt == true)
	  {
		stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
		callFromIFStmt = false;
		
		BaseStmtVisitor::Visit(stmt);
		return;
	  }
	//rank && int
       }else if(hasOneRank(BO) == true && strcmp(BO->getOpcodeStr(), and_bin.c_str()) == 0)
       {
	  callFromIFStmt = false;
	  
       //both no ranks and && or ||
       }else if(BinaryOperator *BO_LHS = dyn_cast<BinaryOperator>(BO->getLHS()))
       {
	 if(BinaryOperator *BO_RHS = dyn_cast<BinaryOperator>(BO->getRHS()))
	 {
	   if(hasOneRank(BO_RHS) == false && hasOneRank(BO_LHS) == false &&
	     (strcmp(BO->getOpcodeStr(), and_bin.c_str()) == 0 || strcmp(BO->getOpcodeStr(), or_bin.c_str()) == 0))
	     {
		if(callFromIFStmt == true)
		{
		    stackOfChoiceNodes.top() = putChoiceNodeAndRoot(choice_nodes);
		    callFromIFStmt = false;
		}
			  
		BaseStmtVisitor::Visit(stmt);
		return;
	    }
	 }
       }
       
       
       //check if both sides of binary operator "||" have "rank != int" - supposing that (rank != x || rank != y): x not the same as y
       if (hasTwoRanks(BO) == true && strcmp(BO->getOpcodeStr(), or_bin.c_str()) == 0)
       {
	 if(BinaryOperator *BO_LHS = dyn_cast<BinaryOperator>(BO->getLHS())){
	   if(BinaryOperator *BO_RHS = dyn_cast<BinaryOperator>(BO->getRHS())){
	     if(strcmp(BO_LHS->getOpcodeStr(), neq.c_str()) == 0 && strcmp(BO_RHS->getOpcodeStr(), neq.c_str()) == 0){
	       
	         BaseStmtVisitor::Visit(stmt);
		 return;
	      }
	   }
	  }
       }
       
       
       //if there is not parenthesis in LHS of binary operator
       if(isLHSParen == false)
       {
	  //check LHS Of binary operators
	  if(isa<BinaryOperator>(BO) && (strcmp(BO->getOpcodeStr(), or_bin.c_str()) == 0 || strcmp(BO->getOpcodeStr(), and_bin.c_str()) == 0))
	  {     
	    BinaryOperator *BO1 = dyn_cast<BinaryOperator>(BO->getLHS());
	    
	    visitAllOtherBinOps(BO1, stmt, callFromIFStmt, choice_nodes);
	    
	  } else if(isa<ImplicitCastExpr>(BO->getLHS()))
	  { 
	    if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getLHS())){
	       if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
		   if(VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
	               if(isRankName(VD->getNameAsString())){
			 
			    visitTree(BO, stmt ,getRank(BO));
			}
		   }
	       }
	    }
	  } 
       }
	
	
	////if there is not parenthesis in RHS of binary operator
       if(isRHSParen == false)
       {
	  //check RHS  of binary operators
	  if(isa<BinaryOperator>(BO) && (strcmp(BO->getOpcodeStr(), or_bin.c_str()) == 0 || strcmp(BO->getOpcodeStr(), and_bin.c_str()) == 0))
	  {     
	    BinaryOperator *BO2 = dyn_cast<BinaryOperator>(BO->getRHS());
	    
	    visitAllOtherBinOps(BO2, stmt, callFromIFStmt, choice_nodes);
	    
	  } else if(isa<ImplicitCastExpr>(BO->getRHS()))
	  {   
	    if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getRHS())){
	       if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
		   if(VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
	               if(isRankName(VD->getNameAsString())){
			 
			    visitTree(BO, stmt ,getRank(BO));
			}
		   }
	       }
	    }
	  }   
       }
   }
      

    //get datatype from MPI primitives
    std::string get_MPI_Datatype(Expr *expr) {
        std::string MPI_Datatype("");
	
	if (isa<ParenExpr>(expr)) {
	  if(ParenExpr *PE = dyn_cast<ParenExpr>(expr)) {
	    if (CStyleCastExpr *CSCE = dyn_cast<CStyleCastExpr>(PE->getSubExpr())) {
	      if (IntegerLiteral *IL = dyn_cast<IntegerLiteral>(CSCE->getSubExpr())) {
		if (IL->getValue() == static_cast<uint64_t>(1275069445)) //check if is MPI_INT
		{
		    MPI_Datatype = "MPI_INT";
		} else if (IL->getValue() == static_cast<uint64_t>(1275068673)) //check if is MPI_CHAR
		{
		    MPI_Datatype = "MPI_CHAR";
		} else if (IL->getValue() == static_cast<uint64_t>(1275069450))
		{
		    MPI_Datatype = "MPI_FLOAT";
		} else if (IL->getValue() == static_cast<uint64_t>(1275070471))
		{
		    MPI_Datatype = "MPI_LONG";
		} else if (IL->getValue() == static_cast<uint64_t>(1275070475))
		{
		    MPI_Datatype = "MPI_DOUBLE";
		}
		else {
		    llvm::errs() << "Warning: unable to recognize datatype - " << *(IL->getValue().getRawData()) << "\n";
		    MPI_Datatype = "MPI_DATATYPE_NOT_RECOGNISED";
		}
	      }
	    }
	  }
	} else { //No MPI_Datatype
          llvm::errs() << "Warning: unable to extract datatype\n";
          MPI_Datatype = std::string("MPI_Datatype_EXTRACT_ERROR");
        }
        
	return MPI_Datatype;
    } 
    
      /* Visitors------------------------------------------------------------ */

      // Generic visitor.
      void Visit(Decl *decl) {
        if (!decl) return;
	
        Decl *prev_decl = current_decl_;
        current_decl_ = decl;
        BaseDeclVisitor::Visit(decl);
        current_decl_ = prev_decl;
      }

      // Declarator (variable | function | struct | typedef) visitor.
      void VisitDeclaratorDecl(DeclaratorDecl *decl_decl) {
        BaseDeclVisitor::VisitDeclaratorDecl(decl_decl);
      }

      // Declaration visitor.
      void VisitDecl(Decl *D) {
        if (isa<FunctionDecl>(D) || isa<ObjCMethodDecl>(D) || isa<BlockDecl>(D))
          return;

        // Generate context from declaration.
        if (DeclContext *DC = dyn_cast<DeclContext>(D))
          cast<MPITypeCheckingConsumer>(this)->VisitDeclContext(DC);
      }

      // Declaration context visitor.
      void VisitDeclContext(DeclContext *DC) {
        for (DeclContext::decl_iterator
             iter = DC->decls_begin(), iter_end = DC->decls_end();
             iter != iter_end; ++iter) {
          Visit(*iter);
        }
      }

      // Variable visitor.
      void VisitDeclRefExpr(DeclRefExpr* expr) {
      }

      // Function (declaration and body) visitor.
      void VisitFunctionDecl(FunctionDecl *D) {
	//if we are in main then we can visit the rest function inside it (visitNow)
        if(D->isMain())
        {
          visitNow = true;
        }
        
        if(visitNow == true)
        {
          BaseDeclVisitor::VisitFunctionDecl(D);
          if (D->isThisDeclarationADefinition()) {
            BaseStmtVisitor::Visit(D->getBody());
          }
        }
        
        visitNow =false;
      }

      // Generic code block (declaration and body) visitor.
      void VisitBlockDecl(BlockDecl *D) {
        BaseDeclVisitor::VisitBlockDecl(D);
        BaseStmtVisitor::Visit(D->getBody());
      }

      // Variable declaration visitor.
      void VisitVarDecl(VarDecl *D) {
        BaseDeclVisitor::VisitVarDecl(D);

        // If variable is a role, keep track of it.
        if (src_mgr_->isFromMainFile(D->getLocation())
            && D->getType().getAsString() == "role *") {

          if (D->hasInit()) {
            //-varname2rolename[D->getNameAsString()] = get_rolename(D->getInit());
          } else {
            llvm::errs()
              << "Warn: role* declaration not allowed without initialiser!"
              << "Declaration ignored\n";
          }
          return; // Skip over the initialiser Visitor.
        }

        // Initialiser.
        if (Expr *Init = D->getInit())
          BaseStmtVisitor::Visit(Init);
      }

      /* Statement Visitors-------------------------------------------------- */

      void VisitDeclStmt(DeclStmt *stmt) {
        for (DeclStmt::decl_iterator
             iter = stmt->decl_begin(), iter_end = stmt->decl_end();
             iter != iter_end; ++iter)
          Visit(*iter);
      }

      void VisitBlockExpr(BlockExpr *expr) {
        // The BlockDecl is also visited by 'VisitDeclContext()'.
        // No need to visit it twice.
      }

      // Statement visitor.
      void VisitStmt(Stmt *stmt) {
        // Function call statement.
        if (isa<CallExpr>(stmt)) { // FunctionCall
          CallExpr *callExpr = cast<CallExpr>(stmt);

          if (callExpr->getDirectCallee() != 0) {

            //
            // Order of evaluating a function CALL is different from
            // the order in the AST
            // We want to make sure the arguments are evaluated first
            // in a function call, before evaluating the func call itself
            //
        
            Stmt *func_call_stmt = NULL;
            std::string func_name(callExpr->getDirectCallee()->getNameAsString());
            std::string datatype;
	    std::string datatype2;
            std::string role;
            std::string label;

            for (Stmt::child_iterator
                iter = stmt->child_begin(), iter_end = stmt->child_end();
                iter != iter_end; ++iter) {

                // Skip first child (FunctionCall Stmt).
                if (func_call_stmt == NULL) {
                func_call_stmt = *iter;
                continue;
                }

                // Visit function arguments.
                if (*iter) BaseStmtVisitor::Visit(*iter);
            }


            // Visit FunctionCall Stmt. 
            BaseStmtVisitor::Visit(func_call_stmt); //
	    
	    
	     // ---------- Initialisation ----------
            if (func_name.find("MPI_Init") != std::string::npos) {
	      
	      // ------- Comment the following code if no MPI_Init and uncomment the code on initialization
	      std::vector<st_tree*>::iterator it1 = end_trees.begin();
	      std::vector< std::stack<st_node*> >::iterator it2 = appendto_nodes.begin();
	      
	      while(it1 != end_trees.end() && it2 != appendto_nodes.end())
	      {	  
		  //copy stack from vector to a temporary stack
		  std::stack<st_node*> tmp_stack = *it2;
		  st_node* tmp_st_node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_ROOT);;
		  
		  (*it1)->root = tmp_st_node;
		  tmp_stack.push(tmp_st_node);
		  //update stack
		  *it2 = tmp_stack;
		 
		  it1++;
		  it2++;
	      }
	      
	      
	      // Parse the Scribble file.
              yyin = fopen(scribbleFilePath.c_str(), "r");
              scribble_tree_ = st_tree_init((st_tree *)malloc(sizeof(st_tree)));
              if (yyin == NULL) {
                llvm::errs() << "Unable to open Scribble file.\n";
              } else {
                yyparse(scribble_tree_);
              }
              fclose(yyin);

              if (scribble_tree_ == NULL) { // ie. parse failed
                llvm::errs() << "ERROR: Unable to parse Scribble file.\n";
                return;
              }
              
	      return;
	  }
	    
	    // ------- MPI_Finalize ------------
            if (func_name.find("MPI_Finalize") != std::string::npos) {

              return;
            }
            
            // ------ MPI_Comm_rank ------------
            if (func_name.find("MPI_Comm_rank") != std::string::npos)
	    {
		//get 2nd argument of method
		if(isa<UnaryOperator>(callExpr->getArg(1))){
		  if(UnaryOperator *UO = dyn_cast<UnaryOperator>(callExpr->getArg(1))){
		    if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(UO->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			    //put name on vector with "rank variable" names
			    rankNames.push_back(VD->getNameAsString());
			}
		    }
		  } 
		}
		
		return;
	    }
	    
	    // --------- MPI_SEND --------------
	    if (func_name.find("MPI_Send") != std::string::npos)
	    { 
	       std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	       
		while(it != appendto_nodes.end())
		{	  
		  if((*it).empty())
		  {
		    llvm::errs() << "\nWarning: Tree (stack) empty. Some MPI primitive might be before MPI_Init. Current method MPI_Send.\n";
		  }
		  it++;
		}
		
		std::ostringstream tmp_oss_to;
		std::ostringstream tmp_oss_tag;
		
		std::string tmp_str_to;
		std::string tmp_str_tag;
		
		datatype = get_MPI_Datatype(callExpr->getArg(2));
		
		//get 4th argument of primitive
		if(isa<BinaryOperator>(callExpr->getArg(3))){
		  if(BinaryOperator *BO = dyn_cast<BinaryOperator>(callExpr->getArg(3))){
		    
		    //get var name
		    if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getLHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_to = VD->getNameAsString();
			}
		      }
		    }
		    
		    //get binary operator
		    tmp_str_to += BO->getOpcodeStr();
		    
		    //get integer
		    if(IntegerLiteral *IL = dyn_cast<IntegerLiteral>(BO->getRHS())){
		       const uint64_t* tmp_num_to = IL->getValue().getRawData();
		
		      //convert uint64_t to strd::string
		      tmp_oss_to<< *tmp_num_to;
		      tmp_str_to += tmp_oss_to.str();
		      
		     //if RHS of operator is also a variable
		    }else if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getRHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_to += VD->getNameAsString();
			}
		      }
		    }
		    
		  }
		}
		else if(isa<ImplicitCastExpr>(callExpr->getArg(3)))
		{
		  if(ImplicitCastExpr *ICE_ARG3 = dyn_cast<ImplicitCastExpr>(callExpr->getArg(3)))
		  {
		    //if var if not initialised
		    if(getRankNum(ICE_ARG3) == -2)
		    {
			if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE_ARG3->getSubExpr())){
			  if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			    tmp_str_to = VD->getNameAsString();
			  } 
			}
		      
		    }else{
		    //convert int to string
		     tmp_oss_to << getRankNum(ICE_ARG3);
		     tmp_str_to += tmp_oss_to.str();
		    }
		  }
		  
		} else if (isa<IntegerLiteral>(callExpr->getArg(3)))
		{
		  const uint64_t* tmp_to = dyn_cast<IntegerLiteral>(callExpr->getArg(3))->getValue().getRawData();
		 
		  //convert uint64_t to strd::string
		  tmp_oss_to << *tmp_to;
		  tmp_str_to += tmp_oss_to.str();
		  
		}else{
		    
		  tmp_str_to = "Warning: from/to/root not maching any type.";
		}
		
		//get 5th argument of primitive
		if(isa<ImplicitCastExpr>(callExpr->getArg(4)))
		{
		  if(ImplicitCastExpr *ICE_ARG4 = dyn_cast<ImplicitCastExpr>(callExpr->getArg(4)))
		  {
		     //convert int to string
		     tmp_oss_tag << getRankNum(ICE_ARG4);
		     tmp_str_tag += tmp_oss_tag.str();
		  }
		  
		} else if (isa<IntegerLiteral>(callExpr->getArg(4)))
		{
		  const uint64_t* tmp_tag = dyn_cast<IntegerLiteral>(callExpr->getArg(4))->getValue().getRawData();
		  
		  //convert uint64_t to strd::string
		  tmp_oss_tag << *tmp_tag;
		  tmp_str_tag += tmp_oss_tag.str(); 
		}else
		{  
		  tmp_str_tag = "Warning: from/to/root not maching any type.";
		}
		
		st_node *node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_SEND);
		
		updateTree(node, tmp_str_to, tmp_str_tag, datatype, "");
                 
                return;
	      }
	    
	    
	    // --------- MPI_ISEND --------------
	    if (func_name.find("MPI_Isend") != std::string::npos)
	    {
	       std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	       
		while(it != appendto_nodes.end())
		{	  
		  if((*it).empty())
		  {
		    llvm::errs() << "\nWarning: Tree (stack) empty. Some MPI primitive might be before MPI_Init. Current method MPI_Isend.\n";
		  }
		  it++;
		}
		
		std::ostringstream tmp_oss_to;
		std::ostringstream tmp_oss_tag;
		
		std::string tmp_str_to;
		std::string tmp_str_tag;
		
		datatype = get_MPI_Datatype(callExpr->getArg(2));
		
		//get 4th argument of primitive
		if(isa<BinaryOperator>(callExpr->getArg(3))){
		  if(BinaryOperator *BO = dyn_cast<BinaryOperator>(callExpr->getArg(3))){
		    
		    //get var name
		    if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getLHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_to = VD->getNameAsString();
			}
		      }
		    }
		    
		    //get binary operator
		    tmp_str_to += BO->getOpcodeStr();
		    
		    //get integer
		    if(IntegerLiteral *IL = dyn_cast<IntegerLiteral>(BO->getRHS())){
		       const uint64_t* tmp_num_to = IL->getValue().getRawData();
		
		      //convert uint64_t to strd::string
		      tmp_oss_to<< *tmp_num_to;
		      tmp_str_to += tmp_oss_to.str();
		      
		     //if RHS of operator is also a variable
		    }else if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getRHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_to += VD->getNameAsString();
			}
		      }
		    }
		    
		  }
		}
		else if(isa<ImplicitCastExpr>(callExpr->getArg(3)))
		{
		  if(ImplicitCastExpr *ICE_ARG3 = dyn_cast<ImplicitCastExpr>(callExpr->getArg(3)))
		  {
		    //if var if not initialised
		    if(getRankNum(ICE_ARG3) == -2)
		    {
			if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE_ARG3->getSubExpr())){
			  if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			    tmp_str_to = VD->getNameAsString();
			  } 
			}
		      
		    }else{
		    //convert int to string
		     tmp_oss_to << getRankNum(ICE_ARG3);
		     tmp_str_to += tmp_oss_to.str();
		    }
		  }
		  
		} else if (isa<IntegerLiteral>(callExpr->getArg(3)))
		{
		  const uint64_t* tmp_to = dyn_cast<IntegerLiteral>(callExpr->getArg(3))->getValue().getRawData();
		 
		  //convert uint64_t to strd::string
		  tmp_oss_to << *tmp_to;
		  tmp_str_to += tmp_oss_to.str();
		  
		}else{
		    
		  tmp_str_to = "Warning: from/to/root not maching any type.";
		}
		
		//get 5th argument of primitive
		if(isa<ImplicitCastExpr>(callExpr->getArg(4)))
		{
		  if(ImplicitCastExpr *ICE_ARG4 = dyn_cast<ImplicitCastExpr>(callExpr->getArg(4)))
		  {
		     //convert int to string
		     tmp_oss_tag << getRankNum(ICE_ARG4);
		     tmp_str_tag += tmp_oss_tag.str();
		  }
		  
		} else if (isa<IntegerLiteral>(callExpr->getArg(4)))
		{
		  const uint64_t* tmp_tag = dyn_cast<IntegerLiteral>(callExpr->getArg(4))->getValue().getRawData();
		  
		  //convert uint64_t to strd::string
		  tmp_oss_tag << *tmp_tag;
		  tmp_str_tag += tmp_oss_tag.str(); 
		}else
		{  
		  tmp_str_tag = "Warning: from/to/root not maching any type.";
		}
		
	        st_node *node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_ISEND);
                
		updateTree(node, tmp_str_to, tmp_str_tag, datatype, "");
               
                return;
	      }

	      // ---------- MPI_Bcast ----------
            if (func_name.find("MPI_Bcast") != std::string::npos) 
	    {
	        std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	       
		while(it != appendto_nodes.end())
		{	  
		  if((*it).empty())
		  {
		    llvm::errs() << "\nWarning: Tree (stack) empty. Some MPI primitive might be before MPI_Init. Current method MPI_	Bcast.\n";
		  }
		  it++;
		}
	      
		std::ostringstream tmp_oss_from;
		std::string tmp_str_from;
		std::string tmp_str_tag = "-";
		
		datatype = get_MPI_Datatype(callExpr->getArg(2));
		
		//get 4th argument of primitive
		if(isa<BinaryOperator>(callExpr->getArg(3))){
		  if(BinaryOperator *BO = dyn_cast<BinaryOperator>(callExpr->getArg(3))){
		    
		    //get var name
		    if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getLHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_from = VD->getNameAsString();
			}
		      }
		    }
		    
		    //get binary operator
		    tmp_str_from += BO->getOpcodeStr();
		    
		    //get integer
		    if(IntegerLiteral *IL = dyn_cast<IntegerLiteral>(BO->getRHS())){
		       const uint64_t* tmp_num_from = IL->getValue().getRawData();
		
		      //convert uint64_t to strd::string
		      tmp_oss_from << *tmp_num_from;
		      tmp_str_from += tmp_oss_from.str();
		      
		     //if RHS of operator is also a variable
		    }else if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getRHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_from += VD->getNameAsString();
			}
		      }
		    }
		    
		  }
		}
		else if(isa<ImplicitCastExpr>(callExpr->getArg(3)))
		{
		  if(ImplicitCastExpr *ICE_ARG3 = dyn_cast<ImplicitCastExpr>(callExpr->getArg(3)))
		  {
		    //if var if not initialised
		    if(getRankNum(ICE_ARG3) == -2)
		    {
			if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE_ARG3->getSubExpr())){
			  if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			    tmp_str_from = VD->getNameAsString();
			  } 
			}
		      
		    }else{
		    //convert int to string
		     tmp_oss_from << getRankNum(ICE_ARG3);
		     tmp_str_from += tmp_oss_from.str();
		    }
		  }
		  
		} else if (isa<IntegerLiteral>(callExpr->getArg(3)))
		{
		  const uint64_t* tmp_from = dyn_cast<IntegerLiteral>(callExpr->getArg(3))->getValue().getRawData();
		
		  //convert uint64_t to strd::string
		  tmp_oss_from << *tmp_from;
		  tmp_str_from += tmp_oss_from.str();
		  
		}else
		{
		  tmp_str_from = "Warning: from/to/root not maching any type.";
		}
		
		st_node *node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_BCAST);
		
		if(isIfStmt == true)
                {
		   isCollectiveOper = true;
		   collectiveOperRoot = atoi(tmp_str_from.c_str());
                   updateTree(node, tmp_str_from, tmp_str_tag, datatype, "");
		   isCollectiveOper = false;
		}else{
		  collectiveOperRoot = atoi(tmp_str_from.c_str());
		  updateTree_collectiveOper(node, tmp_str_from, tmp_str_tag, datatype, "");
		}
		
                return;
            }
	      
            
            // ---------- MPI_Recv ----------
            if (func_name.find("MPI_Recv") != std::string::npos) 
	    {
	        std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	       
		while(it != appendto_nodes.end())
		{	  
		  if((*it).empty())
		  {
		    llvm::errs() << "\nWarning: Tree (stack) empty. Some MPI primitive might be before MPI_Init. Current method MPI_Recv.\n";
		  }
		  it++;
		}
	      
		std::ostringstream tmp_oss_from;
		std::ostringstream tmp_oss_tag;
		
		std::string tmp_str_from;
		std::string tmp_str_tag;
		
		datatype = get_MPI_Datatype(callExpr->getArg(2));
		
		//get 4th argument of primitive
		if(isa<BinaryOperator>(callExpr->getArg(3))){
		  if(BinaryOperator *BO = dyn_cast<BinaryOperator>(callExpr->getArg(3))){
		    
		    //get var name
		    if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getLHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_from = VD->getNameAsString();
			}
		      }
		    }
		    
		    //get binary operator
		    tmp_str_from += BO->getOpcodeStr();
		    
		    //get integer
		    if(IntegerLiteral *IL = dyn_cast<IntegerLiteral>(BO->getRHS())){
		       const uint64_t* tmp_num_from = IL->getValue().getRawData();
		
		      //convert uint64_t to strd::string
		      tmp_oss_from << *tmp_num_from;
		      tmp_str_from += tmp_oss_from.str();
		      
		     //if RHS of operator is also a variable
		    }else if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getRHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_from += VD->getNameAsString();
			}
		      }
		    }
		    
		  }
		}
		else if(isa<ImplicitCastExpr>(callExpr->getArg(3)))
		{
		  if(ImplicitCastExpr *ICE_ARG3 = dyn_cast<ImplicitCastExpr>(callExpr->getArg(3)))
		  {
		    //if var if not initialised
		    if(getRankNum(ICE_ARG3) == -2)
		    {
			if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE_ARG3->getSubExpr())){
			  if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			    tmp_str_from = VD->getNameAsString();
			  } 
			}
		      
		    }else{
		    //convert int to string
		     tmp_oss_from << getRankNum(ICE_ARG3);
		     tmp_str_from += tmp_oss_from.str();
		    }
		  }
		  
		} else if (isa<IntegerLiteral>(callExpr->getArg(3)))
		{
		  const uint64_t* tmp_from = dyn_cast<IntegerLiteral>(callExpr->getArg(3))->getValue().getRawData();
		
		  //convert uint64_t to strd::string
		  tmp_oss_from << *tmp_from;
		  tmp_str_from += tmp_oss_from.str();
		  
		}else
		{
		  tmp_str_from = "Warning: from/to/root not maching any type.";
		}
		
		
		//get 5th argument of primitive
		if(isa<ImplicitCastExpr>(callExpr->getArg(4)))
		{
		  if(ImplicitCastExpr *ICE_ARG4 = dyn_cast<ImplicitCastExpr>(callExpr->getArg(4)))
		  {
		     //convert int to string
		     tmp_oss_tag << getRankNum(ICE_ARG4);
		     tmp_str_tag += tmp_oss_tag.str();
		  }
		  
		} else if (isa<IntegerLiteral>(callExpr->getArg(4)))
		{
		  const uint64_t* tmp_tag = dyn_cast<IntegerLiteral>(callExpr->getArg(4))->getValue().getRawData();
		  
		  //convert uint64_t to strd::string
		  tmp_oss_tag << *tmp_tag;
		  tmp_str_tag += tmp_oss_tag.str(); 
		}else
		{  
		  tmp_str_tag = "Warning: from/to/root not maching any type.";
		}
		
	        st_node *node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_RECV);
		
		updateTree(node, tmp_str_from, tmp_str_tag, datatype, "");
                
                return;
            }
            
            // ---------- MPI_IRecv ----------
            if (func_name.find("MPI_Irecv") != std::string::npos) 
	    {
	        std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	       
		while(it != appendto_nodes.end())
		{	  
		  if((*it).empty())
		  {
		    llvm::errs() << "\nWarning: Tree (stack) empty. Some MPI primitive might be before MPI_Init. Current method MPI_Irecv.\n";
		  }
		  it++;
		}
	      
		std::ostringstream tmp_oss_from;
		std::ostringstream tmp_oss_tag;
		
		std::string tmp_str_from;
		std::string tmp_str_tag;
		
		datatype = get_MPI_Datatype(callExpr->getArg(2));
		
		//get 4th argument of primitive
		if(isa<BinaryOperator>(callExpr->getArg(3))){
		  if(BinaryOperator *BO = dyn_cast<BinaryOperator>(callExpr->getArg(3))){
		    
		    //get var name
		    if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getLHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_from = VD->getNameAsString();
			}
		      }
		    }
		    
		    //get binary operator
		    tmp_str_from += BO->getOpcodeStr();
		    
		    //get integer
		    if(IntegerLiteral *IL = dyn_cast<IntegerLiteral>(BO->getRHS())){
		       const uint64_t* tmp_num_from = IL->getValue().getRawData();
		
		      //convert uint64_t to strd::string
		      tmp_oss_from << *tmp_num_from;
		      tmp_str_from += tmp_oss_from.str();
		      
		     //if RHS of operator is also a variable
		    }else if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getRHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_from += VD->getNameAsString();
			}
		      }
		    }
		    
		  }
		}
		else if(isa<ImplicitCastExpr>(callExpr->getArg(3)))
		{
		  if(ImplicitCastExpr *ICE_ARG3 = dyn_cast<ImplicitCastExpr>(callExpr->getArg(3)))
		  {
		    //if var if not initialised
		    if(getRankNum(ICE_ARG3) == -2)
		    {
			if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE_ARG3->getSubExpr())){
			  if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			    tmp_str_from = VD->getNameAsString();
			  } 
			}
		      
		    }else{
		    //convert int to string
		     tmp_oss_from << getRankNum(ICE_ARG3);
		     tmp_str_from += tmp_oss_from.str();
		    }
		  }
		  
		} else if (isa<IntegerLiteral>(callExpr->getArg(3)))
		{
		  const uint64_t* tmp_from = dyn_cast<IntegerLiteral>(callExpr->getArg(3))->getValue().getRawData();
		
		  //convert uint64_t to strd::string
		  tmp_oss_from << *tmp_from;
		  tmp_str_from += tmp_oss_from.str();
		  
		}else
		{
		  tmp_str_from = "Warning: from/to/root not maching any type.";
		}
		
		
		//get 5th argument of primitive
		if(isa<ImplicitCastExpr>(callExpr->getArg(4)))
		{
		  if(ImplicitCastExpr *ICE_ARG4 = dyn_cast<ImplicitCastExpr>(callExpr->getArg(4)))
		  {
		     //convert int to string
		     tmp_oss_tag << getRankNum(ICE_ARG4);
		     tmp_str_tag += tmp_oss_tag.str();
		  }
		  
		} else if (isa<IntegerLiteral>(callExpr->getArg(4)))
		{
		  const uint64_t* tmp_tag = dyn_cast<IntegerLiteral>(callExpr->getArg(4))->getValue().getRawData();
		  
		  //convert uint64_t to strd::string
		  tmp_oss_tag << *tmp_tag;
		  tmp_str_tag += tmp_oss_tag.str(); 
		}else
		{  
		  tmp_str_tag = "Warning: from/to/root not maching any type.";
		}
		

	        st_node *node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_IRECV);
                
		updateTree(node, tmp_str_from, tmp_str_tag, datatype, "");
		
                return;
            }
        
	    
	    // ---------- MPI_Reduce ----------
            if (func_name.find("MPI_Reduce") != std::string::npos) 
	    {
	        std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	       
		while(it != appendto_nodes.end())
		{	  
		  if((*it).empty())
		  {
		    llvm::errs() << "\nWarning: Tree (stack) empty. Some MPI primitive might be before MPI_Init. Current method MPI_Reduce.\n";
		  }
		  it++;
		}
	      
		std::ostringstream tmp_oss_to;
		std::string tmp_str_to;
		std::string tmp_str_tag = "-";
		
		datatype = get_MPI_Datatype(callExpr->getArg(3));
		
		//get 6th argument of primitive
		if(isa<BinaryOperator>(callExpr->getArg(5))){
		  if(BinaryOperator *BO = dyn_cast<BinaryOperator>(callExpr->getArg(5))){
		    
		    //get var name
		    if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getLHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_to = VD->getNameAsString();
			}
		      }
		    }
		    
		    //get binary operator
		    tmp_str_to += BO->getOpcodeStr();
		    
		    //get integer
		    if(IntegerLiteral *IL = dyn_cast<IntegerLiteral>(BO->getRHS())){
		       const uint64_t* tmp_num_to = IL->getValue().getRawData();
		
		      //convert uint64_t to strd::string
		      tmp_oss_to<< *tmp_num_to;
		      tmp_str_to += tmp_oss_to.str();
		      
		     //if RHS of operator is also a variable
		    }else if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getRHS())){
		      if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			   tmp_str_to += VD->getNameAsString();
			}
		      }
		    }
		    
		  }
		}
		else if(isa<ImplicitCastExpr>(callExpr->getArg(5)))
		{
		  if(ImplicitCastExpr *ICE_ARG3 = dyn_cast<ImplicitCastExpr>(callExpr->getArg(5)))
		  {
		    //if var if not initialised
		    if(getRankNum(ICE_ARG3) == -2)
		    {
			if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE_ARG3->getSubExpr())){
			  if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			    tmp_str_to = VD->getNameAsString();
			  } 
			}
		      
		    }else{
		    //convert int to string
		     tmp_oss_to << getRankNum(ICE_ARG3);
		     tmp_str_to += tmp_oss_to.str();
		    }
		  }
		  
		} else if (isa<IntegerLiteral>(callExpr->getArg(5)))
		{
		  const uint64_t* tmp_to = dyn_cast<IntegerLiteral>(callExpr->getArg(5))->getValue().getRawData();
		 
		  //convert uint64_t to strd::string
		  tmp_oss_to << *tmp_to;
		  tmp_str_to += tmp_oss_to.str();
		  
		}else{
		    
		  tmp_str_to = "Warning: from/to/root not maching any type.";
		}
		
		st_node *node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_REDUCE);
		
                if(isIfStmt == true)
                {
		   isCollectiveOper = true;
		   collectiveOperRoot = atoi(tmp_str_to.c_str());
                  updateTree(node, tmp_str_to, tmp_str_tag, datatype, "");
		  isCollectiveOper = false;
                }else{
		  collectiveOperRoot = atoi(tmp_str_to.c_str());
		  updateTree_collectiveOper(node, tmp_str_to, tmp_str_tag, datatype, "");
		}
		
                return;
            }
            
            //visit all other functions except the primitives above
            VisitFunctionDecl(callExpr->getDirectCallee());
	    
            
          } else {
            //
            // With the exception of role-extraction function, ignore all non-direct function calls.
            //
            if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(callExpr->getCallee())) {
              if (ICE->getType().getAsString().compare("role *(*)(struct session_t *, char *)") != 0) {
                llvm::errs() << "Warn: Skipping over a non-direct function call\n";
                callExpr->dump();
              }
            }

          } // if direct function call

        } // if isa<CallExpr>                          

	  
        // While statement.
        if (isa<WhileStmt>(stmt)) {
          WhileStmt *whileStmt = cast<WhileStmt>(stmt);
	  
	  st_node *node;
	  std::string loopLabel;
	  std::vector<st_node*> recur_nodes;
	  std::vector<std::string> looplabels_vect;
	  
	  recur_nodes.resize(appendto_nodes.size());
	  looplabels_vect.resize(appendto_nodes.size());
	  
	  std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	  std::vector<st_node*>::iterator it1 = recur_nodes.begin();
	  std::vector<std::string>::iterator loolLab_it = looplabels_vect.begin();
	  
	  while(it != appendto_nodes.end())
	  {	
	       node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_RECUR);
	       std::ostringstream ss;
	       ss << "_L" << recur_counter++;
               loopLabel = ss.str();
 	       *loolLab_it = loopLabel;
               node->recur->label = (char *)calloc(sizeof(char), loopLabel.size()+1);
               strcpy(node->recur->label, loopLabel.c_str());
	       
	       *it1 = node;
	       
	       st_node * previous_node = (*it).top();
	       st_node_append(previous_node, node);
	       (*it).push(node);
	       
	       it++;
	       it1++;
	       loolLab_it++;
	  }
	  
          BaseStmtVisitor::Visit(whileStmt->getBody());

	  
          // Implicit continue at end of loop.
          st_node *node_end;
	  
	  std::vector< std::stack<st_node*> >::iterator it2 = appendto_nodes.begin();
	  std::vector<st_node*>::iterator it3 = recur_nodes.begin();
	  std::vector<std::string>::iterator loolLab_it1 = looplabels_vect.begin();
	 
	  while(it2 != appendto_nodes.end())
	  {	
	       node_end = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_CONTINUE);
	       node_end->cont->label = (char *)calloc(sizeof(char), (*loolLab_it1).size()+1);
               strcpy(node_end->cont->label, (*loolLab_it1).c_str());
               st_node_append(*it3, node_end);
		 
	       it2++;
	       it3++;
	       loolLab_it1++;
	  }
	  
          std::vector< std::stack<st_node*> >::iterator it4 = appendto_nodes.begin();
	    
	   //pop stack in order to return to main root node
	   while(it4 != appendto_nodes.end())
	   {
	      (*it4).pop();
	            
	      it4++;
	   }

          return;
        } // isa<WhileStmt>
	
        
        
        // For statememt.
        if (isa<ForStmt>(stmt) ) {
          ForStmt *forStmt = cast<ForStmt>(stmt);

          st_node *node;
	  std::string loopLabel;
	  std::vector<st_node*> recur_nodes;
	  std::vector<std::string> looplabels_vect;
	  
	  recur_nodes.resize(appendto_nodes.size());
	  looplabels_vect.resize(appendto_nodes.size());
	  
	  std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	  std::vector<st_node*>::iterator it1 = recur_nodes.begin();
	  std::vector<std::string>::iterator loolLab_it = looplabels_vect.begin();
	  
	  while(it != appendto_nodes.end())
	  {	
	       node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_RECUR);
	       std::ostringstream ss;
	       ss << "_L" << recur_counter++;
               loopLabel = ss.str();
 	       *loolLab_it = loopLabel;
               node->recur->label = (char *)calloc(sizeof(char), loopLabel.size()+1);
               strcpy(node->recur->label, loopLabel.c_str());
	       
	       *it1 = node;
	       
	       st_node * previous_node = (*it).top();
	       st_node_append(previous_node, node);
	       (*it).push(node);
	       
	       it++;
	       it1++;
	       loolLab_it++;
	  }

          BaseStmtVisitor::Visit(forStmt->getBody());

         // Implicit continue at end of loop.
          st_node *node_end;
	  
	  std::vector< std::stack<st_node*> >::iterator it2 = appendto_nodes.begin();
	  std::vector<st_node*>::iterator it3 = recur_nodes.begin();
	  std::vector<std::string>::iterator loolLab_it1 = looplabels_vect.begin();
	 
	  while(it2 != appendto_nodes.end())
	  {	
	       node_end = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_CONTINUE);
	       node_end->cont->label = (char *)calloc(sizeof(char), (*loolLab_it1).size()+1);
               strcpy(node_end->cont->label, (*loolLab_it1).c_str());
               st_node_append(*it3, node_end);
		 
	       it2++;
	       it3++;
	       loolLab_it1++;
	  }
	  
          std::vector< std::stack<st_node*> >::iterator it4 = appendto_nodes.begin();
	    
	   //pop stack in order to return to main root node
	   while(it4 != appendto_nodes.end())
	   {
	      (*it4).pop();
	            
	      it4++;
	   }

          return;
        } // isa<ForStmt>

        
        // Do statement.
        if (isa<DoStmt>(stmt)) {
          DoStmt *doStmt = cast<DoStmt>(stmt);

          st_node *node;
	  std::string loopLabel;
	  std::vector<st_node*> recur_nodes;
	  std::vector<std::string> looplabels_vect;
	  
	  recur_nodes.resize(appendto_nodes.size());
	  looplabels_vect.resize(appendto_nodes.size());
	  
	  std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	  std::vector<st_node*>::iterator it1 = recur_nodes.begin();
	  std::vector<std::string>::iterator loolLab_it = looplabels_vect.begin();
	  
	  while(it != appendto_nodes.end())
	  {	
	       node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_RECUR);
	       std::ostringstream ss;
	       ss << "_L" << recur_counter++;
               loopLabel = ss.str();
 	       *loolLab_it = loopLabel;
               node->recur->label = (char *)calloc(sizeof(char), loopLabel.size()+1);
               strcpy(node->recur->label, loopLabel.c_str());
	       
	       *it1 = node;
	       
	       st_node * previous_node = (*it).top();
	       st_node_append(previous_node, node);
	       (*it).push(node);
	       
	       it++;
	       it1++;
	       loolLab_it++;
	  }

          BaseStmtVisitor::Visit(doStmt->getBody());

          // Implicit continue at end of loop.
          st_node *node_end;
	  
	  std::vector< std::stack<st_node*> >::iterator it2 = appendto_nodes.begin();
	  std::vector<st_node*>::iterator it3 = recur_nodes.begin();
	  std::vector<std::string>::iterator loolLab_it1 = looplabels_vect.begin();
	 
	  while(it2 != appendto_nodes.end())
	  {	
	       node_end = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_CONTINUE);
	       node_end->cont->label = (char *)calloc(sizeof(char), (*loolLab_it1).size()+1);
               strcpy(node_end->cont->label, (*loolLab_it1).c_str());
               st_node_append(*it3, node_end);
		 
	       it2++;
	       it3++;
	       loolLab_it1++;
	  }
	  
          std::vector< std::stack<st_node*> >::iterator it4 = appendto_nodes.begin();
	    
	   //pop stack in order to return to main root node
	   while(it4 != appendto_nodes.end())
	   {
	      (*it4).pop();
	            
	      it4++;
	   }

          return;
        } // isa<DoStmt>


        // Continue (within while-loop).
       if (isa<ContinueStmt>(stmt)) {
	 
	 //previous nodes vector
	 std::vector<st_node*> prevNodes_vect;
	 prevNodes_vect.resize(appendto_nodes.size());
	 
	 std::vector< std::stack<st_node*> >::iterator appToNodes_it = appendto_nodes.begin();
	 
	 for(std::vector<st_node*>::iterator it = prevNodes_vect.begin(); it != prevNodes_vect.end();it++)
	 {
	     *it = (*appToNodes_it).top();
	     
	     appToNodes_it++;
	 }
	 
	 std::vector< std::stack<st_node*> > node_parents(appendto_nodes);
	 //node_parents.resize(appendto_nodes.size());
	 /*std::vector< std::stack<st_node*> >::iterator nodesPar_it = node_parents.begin();
	 
	 for(std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin(); it != appendto_nodes.end();it++)
	 {
	   *nodesPar_it = *it;
	   
	   nodesPar_it++;
	 }*/
	 
	 
	 std::vector<st_node*>::iterator prevNodes_vect_it = prevNodes_vect.begin();
	 //in which tree we are currently
	 int cur_tree = 0;
	 std::list<int> tmp_ranksList;
	 
	 if(!stackOfRanks.empty())
	 {
	    tmp_ranksList = stackOfRanks.top();
	 }
	 
	 for(std::vector< std::stack<st_node*> >::iterator it = node_parents.begin(); it != node_parents.end(); it++)
	 {
	   while(!(*it).empty())
	   {
	     st_node *prev = (*it).top();
	     
	     //if prev node is RECUR node and current tree to write is in rank list
	     if (prev->type == ST_NODE_RECUR && isInList(tmp_ranksList, cur_tree) == 1)
	     {
		st_node *node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_CONTINUE);
		node->cont->label = (char *)calloc(sizeof(char), strlen(prev->recur->label)+1);
		strcpy(node->cont->label, prev->recur->label);
                st_node_append(*prevNodes_vect_it, node);
		
		break;
	
	     //if prev node is RECUR node and list is empty
	     }else if(prev->type == ST_NODE_RECUR && isInList(tmp_ranksList, cur_tree) == 0)
	     {
	        st_node *node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_CONTINUE);
		node->cont->label = (char *)calloc(sizeof(char), strlen(prev->recur->label)+1);
		strcpy(node->cont->label, prev->recur->label);
                st_node_append(*prevNodes_vect_it, node);
		
		break; 
	     }
	     
	     (*it).pop();
	   }
	   
	   prevNodes_vect_it++;
	   cur_tree++;
	 }
	 
	 return;
        } // isa<ContinueStmt>

   
        // If statement.
        if (isa<IfStmt>(stmt)) {
          IfStmt *ifStmt = cast<IfStmt>(stmt);
	  
	  //we need that to know when to change lvl of indent
	  //useful when havinf ELSE IF statement
	  bool notChangeLvlOfIndt = false;
	  
	  isIfStmt = true;
	 
	  
	  //if is not "else if" statement then create list and push it on stack
	  //if is "else if" statement then you use the previous list (of "if" statement)
	    if(isElseIfStmt == true)
	    {
	      isElseIfStmt = false;
	      notChangeLvlOfIndt = true;
	    }else{
	      lvlOfIndent++;
	    }
	    
	   
	   //push an empty vector to stackOfChoiceNodes to be used later
	   std::vector<st_node*> emptyVector; 
	   stackOfChoiceNodes.push(emptyVector);
	    
	  //list containing the ranks that "will" (in quotes since is empty now) have primitives - in an ELSE
	  std::list<int> ranksToWrite;
	
	  //push list in the stack
	  stackOfRanks.push(ranksToWrite);
	   
	  //needed later in ELSE. It just keeps the choice nodes created
	  std::vector<st_node*> choice_nodes;
          
          // Then-block. Consider it only if not empty.
          if(ifStmt->getThen() != NULL) 
	  {
	      
	    //binary operators
	    std::string eq = "==";
	    std::string neq = "!=";
	    std::string ge = ">=";
	    std::string le = "<=";
	    std::string gre = ">";
	    std::string less = "<";
	    std::string and_bin = "&&";
	    std::string or_bin = "||";
	    
	    //check if ifStmt contais "rank"
	    if(isa<BinaryOperator>(ifStmt->getCond())){
	      if(BinaryOperator *BO = dyn_cast<BinaryOperator>(ifStmt->getCond())){
		if (strcmp(BO->getOpcodeStr(), eq.c_str()) == 0 || strcmp(BO->getOpcodeStr(), neq.c_str()) == 0 
		      || strcmp(BO->getOpcodeStr(), ge.c_str()) == 0 || strcmp(BO->getOpcodeStr(), le.c_str()) == 0
		      || strcmp(BO->getOpcodeStr(), gre.c_str()) == 0 || strcmp(BO->getOpcodeStr(), less.c_str()) == 0)
		{
		  if(ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(BO->getLHS())){
		    if(DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(ICE->getSubExpr())){
			if (VarDecl *VD = dyn_cast<VarDecl>(DRE->getDecl())){
			    //if in the condition there is a variable which is "rank" variable
			    if(isRankName(VD->getNameAsString())){
		
				updateAllInElse = false;
				visitTree(BO, ifStmt->getThen() ,getRank(BO));
				
				//std::cout << "choice nodes empty-single rank" << std::endl; 
			    } else {
			      choice_nodes = putChoiceNodeAndRoot(choice_nodes);
			      //std::cout << "choice nodes NO empty - single cond" << std::endl; 
	
			      updateAllInElse = false;
			      
			      BaseStmtVisitor::Visit(ifStmt->getThen());
			    }
			}
		    }
		  }
		} // if binary operator is && or || which means that we have more that one conditions
		else if (strcmp(BO->getOpcodeStr(), and_bin.c_str()) == 0 || strcmp(BO->getOpcodeStr(), or_bin.c_str()) == 0)
		{
		    updateAllInElse = false;
		    visitAllOtherBinOps(BO, ifStmt->getThen(), true, choice_nodes);  
		    
		    choice_nodes = stackOfChoiceNodes.top();
		    
		    if(choice_nodes.empty())
		    {
			//std::cout << "choice nodes empty-complex rank" << std::endl; 
		    }else{
		      //std::cout << "choice nodes empty-complex cond" << std::endl;  
		    }
		    
		    stackOfChoiceNodes.top().clear();
		}
	     }
	   }
	    
	    if(!choice_nodes.empty())
	    {
	      //std::cout << "pop to get choice node" <<  std::endl; 
	      //pop in order to have choice node as top of stack
	      std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	    
	      while(it != appendto_nodes.end())
	      {
		 (*it).pop();
		      
		 it++;
	      }
	    }else{
	      //std::cout << "NO pop - get choice node block" << std::endl; 
	    }
          }
          
	  
          // Else-block.
          if (ifStmt->getElse() != NULL) {
	    
	    if(!choice_nodes.empty())
	    {
	      //std::cout << "push Root" << std::endl; 
	      st_node *else_node;
	    
	      std::vector< std::stack<st_node *> >::iterator it3 = appendto_nodes.begin();
	      std::vector<st_node*>::iterator it4 = choice_nodes.begin();
	  
	      while(it3 != appendto_nodes.end())
	      {	
		  else_node = st_node_init((st_node *)malloc(sizeof(st_node)), ST_NODE_ROOT);
		  st_node_append((*it4), else_node);
		  (*it3).push(else_node);
	      
		  it3++;
		  it4++;
	      }
	    }else{
	     //std::cout << "NO push root"  << std::endl;  
	    }
	     
	    //if "else" is an IF statement
	    if(isa<IfStmt>(ifStmt->getElse()))
	    {    
	      //std::cout << "ELSE-IF" << std::endl; 
	      
	        isElseIfStmt = true;
		isEntryLvlElseIfStmt = true;
		
		BaseStmtVisitor::Visit(ifStmt->getElse());
		
		isEntryLvlElseIfStmt = false;
		
	    }else {
	      //std::cout << "ELSE" << std::endl; 
	      
	      isEntryLvlElseStmt = true;
	      
	      std::list<int> reversedList;
	      
	      if(lvlOfIndent == 1 && choice_nodes.empty() == false)
	      {
		std::list<int> empty_list;
		reversedList = reverseList(empty_list);
	      }else if(updateAllInElse == true && lvlOfIndent >= 2)
	      {
		std::stack< std::list<int> > tmp_stack = stackOfRanks;
		tmp_stack.pop();
		
		reversedList = tmp_stack.top();
		
		updateAllInElse = false;
	      }else{
		reversedList = reverseList(stackOfRanks.top());
	      }
	      
	   
		for(std::list<int>::iterator revList_it = reversedList.begin(); revList_it != reversedList.end(); revList_it++)
		{
		    //std::cout << "revlist " << *revList_it << std::endl;
		    visitTree_elseStmt(ifStmt->getElse(), *revList_it);
		}
		
		//it must be made false before but just to make sure we do it again
		isEntryLvlElseStmt = false;
	    }

	    if(!choice_nodes.empty())
	    {
	      //std::cout << "pop to get choice node - 2" << std::endl; 
	      
	      //pop to have choice node as top of stack
	      std::vector< std::stack<st_node*> >::iterator it = appendto_nodes.begin();
	    
	      while(it != appendto_nodes.end())
	      {
		  (*it).pop();
		      
		  it++;
	      }
	    }else{
	     //std::cout << "NO pop to get choice node -2 " << std::endl;  
	    }
	  }
	    
	    if(!choice_nodes.empty())
	    {
	      //std::cout << "pop to get node before choice" << std::endl; 
	      
	      //pop to have root node of whole tree as top of the stack
	      std::vector< std::stack<st_node*> >::iterator it5 = appendto_nodes.begin();
	    
	      while(it5 != appendto_nodes.end())
	      {
		  (*it5).pop();
		      
		  it5++;
	      }
	    }else{
	     //std::cout << "NO pop to get node before choice" << std::endl;  
	    }
	    
	    //pop list from rank stacks 
	    if(notChangeLvlOfIndt == false)
	    {
	      stackOfRanks.pop();
	    }
	    
	    //decrease level of indentation
	    if(notChangeLvlOfIndt == false)
	    {
	      lvlOfIndent--;
	    }
	    
	    stackOfChoiceNodes.pop();
	    
	    if(lvlOfIndent  == 0)
	    {
	      isIfStmt = false;
	    }
	      
          return; 
        }


        // Child nodes.

        for (Stmt::child_iterator
             iter = stmt->child_begin(), iter_end = stmt->child_end();
             iter != iter_end; ++iter) {
          if (*iter) {
            BaseStmtVisitor::Visit(*iter);
          }
        }

      } // VisitStmt 
  }; // class MPITypeCheckingConsumer
  

/* -------------------------------------------------------------------------- */

  /**
   * Toplevel Plugin interface to dispatch type checker.
   *
   */
  class MPITypeCheckingAction : public PluginASTAction {
    private:
      //processors number
      std::string num_of_proc_str;
      int num_of_processors;
      std::string scribble_file_path;
    
    protected:

      ASTConsumer *CreateASTConsumer(CompilerInstance &CI, llvm::StringRef) {
        MPITypeCheckingConsumer *checker = new MPITypeCheckingConsumer();
        if (CI.hasASTContext()) {
          checker->Initialise(CI.getASTContext(), num_of_processors, scribble_file_path);
        }
	
        return checker;
      }
      
      //get number of processors to be used from the command line
      bool ParseArgs(const CompilerInstance &CI,
                     const std::vector<std::string>& args) {
        if (args.size() == 0) {
          llvm::outs() << "MPI Type Checker [MPI-type-check] "
                       << "clang plugin\n";
          llvm::outs() << "Missing argument: "
                       << "Please specify both number of processors and scribble file path\n";
          return false;
        }

        if (args.size() == 1) {
	  llvm::outs() << "MPI Type Checker [mpi-type-check] "
                       << "clang plugin\n";
          llvm::outs() << "Missing argument: "
                       << "Please specify both number of processors and scribble file path\n";
          return false;
        }
        
        if(args.size() == 2){
	   num_of_proc_str = std::string(args[0]);
	   num_of_processors = atoi(num_of_proc_str.c_str());
	   
	   scribble_file_path = std::string(args[1]);   
	}
        
        return true;
      }

  }; // class MPITypeCheckingAction
} // (null) namespace

static FrontendPluginRegistry::Add<MPITypeCheckingAction>
X("mpi-type-check", "MPI Type checker");
