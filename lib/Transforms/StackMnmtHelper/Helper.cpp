#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Debug.h"

#include <queue>
#include <stack>
#include <unordered_set>



using namespace llvm;



/*
// Visit the graph rooted at ROOT in a BFS manner iteratively and print out path ID for each edge to the specified output file
void bfsPrint(CallGraphNode::CallRecord *root, std::vector<std::vector<CallGraphNode::CallRecord *> > &paths, std::ostream &ofs) {
    std::queue <CallGraphNode::CallRecord *> q; // Used to keep nodes to visit
    std::unordered_set <CallGraphNode::CallRecord *> labels; // Used to keep a record on nodes which have been visited
    q.push(root);
    labels.insert(root);
    while(!q.empty()) {
	// Dequeue a node v
	CallGraphNode::CallRecord *v = q.front();
	q.pop();
	// Visit all the neighbours of v that have not been visited
	for (CallGraphNode::iterator cgni = v->second->begin(), cgne = v->second->end(); cgni != cgne; cgni++) {
	    //Find a neighbour node w of v
	    CallGraphNode::CallRecord *w = &*cgni;
	    // If w has not been labeled, insert it to the queue and label it
	    if (labels.find(w) == labels.end()) {
		q.push(w); 
		labels.insert(w);
	    }
	    // Find and print out the path ID for v->w edge
	    for (size_t i = 0; i < paths.size(); i++) {
		for (size_t j = 0; j < paths[i].size() - 1; j++) {
		    if ( (v == paths[i][j]) && (w == paths[i][j+1])) {
			if (v->second->getFunction())
			    ofs << v->second->getFunction()->getName().str();
			else 
			    ofs << "externalNode";
			ofs << " ";
			if (w->second->getFunction())
			    ofs << w->second->getFunction()->getName().str();
			else 
			    ofs << "externalNode";
			ofs << " " << i+1 << "\n";
		    }
		}
	    }
	}
    }
}
*/

