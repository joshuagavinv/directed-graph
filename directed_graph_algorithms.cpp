/*
 * Notice that the list of included headers has
 * expanded a little. As before, you are not allowed
 * to add to this.
 */
#include <iostream>
#include <vector>
#include <queue>
#include <stack>
#include <unordered_set>
#include <unordered_map>
#include <set>
#include <array>
#include <list>
#include <forward_list>
#include <deque>
#include <map>
#include <cstddef>
#include <string>
#include <utility>
#include <algorithm>
#include <limits>
#include <optional>
#include <exception>
#include <stdexcept>

#include "directed_graph.hpp"

using std::size_t;
using std::set;
using std::list;
using std::vector;
using std::unordered_map;
using std::unordered_set;
using std::stack;
using std::queue;
using std::prev;
using std::next;
using std::numeric_limits;
using std::min;
using std::pair;
/*
 * Computes whether the input is a Directed Acyclic Graph (DAG).
 * A digraph is a DAG if there is no vertex that has a cycle.
 * A cycle is a non-empty set of [out-]edges that starts at one 
 * vertex, and returns to it.
 */
template <typename vertex>
bool is_dag(const directed_graph<vertex> & direct_graph)  //// Finding is_dag, based on Kahn Algorithm
{
  directed_graph<vertex> graph (direct_graph); // copy directed graph from parameter
  set<vertex> process; // set of all vertices with no incoming edges
  
  for(auto v_it = graph.begin(); v_it!= graph.end(); v_it++) //iterating through graph using vertex_iterator
    if(graph.in_degree(*v_it) == 0) // to check that the vertex have zero in degree
      process.insert(*v_it); // if so, we input it into the process set
  
  while(!process.empty()) // while the set is not empty
  {
    auto current_vertex = *process.begin(); //initialize vertex variable with the front or beginning value of set
    process.erase(current_vertex); // erase the vertex stored in current_vertex
    
    for(auto n_it = graph.nbegin(current_vertex); n_it!= graph.nend(current_vertex); n_it++)// iterating through the neighbours of current_vertex
    {
      if(graph.in_degree(*n_it) == 1) // check to see that the in_degree is equal to 1, (which is the current_vertex)
        process.insert(*n_it); // insert the neighbours to the process set
    }
    graph.remove_vertex(current_vertex);  // remove current vertex from the copy graph
  }
  
  if(graph.num_edges() == 0) // if there's no edge left in the graph
    return true;   // then the directed graph is DAG

  return false; // return false, if there's still some edge left in the graph
}

/*
 * Computes a topological ordering of the vertices.
 * For every vertex u in the order, and any of its
 * neighbours v, v appears later in the order than u.
 */
template <typename vertex>
list<vertex> topological_sort(const directed_graph<vertex> & direct_graph) //find topological order using khan algorithm
{
  directed_graph<vertex> graph (direct_graph);// copy directed graph from parameter
  list <vertex> topological_order; // storing topoplogical order in list
  set<vertex> process; // set of all vertices with no incoming edges
  
  for(auto v_it = graph.begin(); v_it!= graph.end(); v_it++) //iterating through the vertices in the graph using vertex_iterator
    if(graph.in_degree(*v_it) == 0)// to check that the vertex have zero in degree
      process.insert(*v_it);// if so, we input it into the process set
  
  while(!process.empty()) // while set is not empty
  {
    auto current_vertex = *process.begin();//initialize vertex variable with the front or beginning value of set
    process.erase(current_vertex);// erase the vertex stored in current_vertex
    topological_order.push_back(current_vertex); // push the current vertex to the list of topo order
    
    for(auto n_it = graph.nbegin(current_vertex); n_it!= graph.nend(current_vertex); n_it++)// iterating through current vertex neighbour
      if(graph.in_degree(*n_it) == 1)// check to see that the in_degree is equal to 1, (which is the current_vertex)
        process.insert(*n_it);// insert the neighbours to the process set
      
    graph.remove_vertex(current_vertex);// remove current vertex from the copy graph
  }
  
  if(graph.num_edges() == 0) // if there's no edge left in the graph
    return topological_order; // graph is DAG, there's a valid topological order in the graph
    
  
  return list<vertex>(); // return an empty list, indicate error, no topological order
}

/*
 * Given a DAG, computes whether there is a Hamiltonian path.
 * a Hamiltonian path is a path that visits every vertex
 * exactly once.
 */
template <typename vertex>
bool is_hamiltonian_dag(const directed_graph<vertex> & direct_graph) 
{
  if(direct_graph.num_vertices() == 0) // test to see if there's 0 vertex
    return true; //return true, since no vertex can be visited
  
  list<vertex> topological_list = topological_sort(direct_graph); // call topological_sort and store the order in list
  int count = 0; // count variable to keep track number of edge
  
  auto previous_end = prev(topological_list.end());// return iterator position before the end of the list, because we want to compare adjacency
                                                   // adjacency of the iterator and the next one after iterator
  
  for(auto it = topological_list.begin(); it!= previous_end; it++) // iterate through list
    if(direct_graph.adjacent(*it, *(next(it, 1)))) // if vertex adjacent to the next vertex on the graph
      count++; // add number of count
  
  if(count ==topological_list.size() - 1) //if the number of count is equal to list size -1, since for the vertex to be visited once
    return true;                // they can only be with 1 edge, with another vertex, thus number of edge ( SIZE -1)
  
  return false; // if not then the directed graph is not Hamitolnian dag
}

template <typename vertex>
vector<vertex> depth_first(const directed_graph<vertex>& direct_graph, const vertex& start_vertex)// traversal algorithm for components
{
  directed_graph<vertex> graph (direct_graph); // copy graph
  vector<vertex>  df_order; // vector storing depth first traversal order
  unordered_set<vertex> visited; // unordered set, marking visit
	stack<vertex> unprocessed; // stack used for depth first
	
	unprocessed.push(start_vertex); // pushing start vertex
  
  while(!unprocessed.empty()) // while not empty
  {
     vertex current_vertex = unprocessed.top(); // make current vertex top of the stack
     unprocessed.pop(); // remove current_vertex from the stack
    
     if(visited.count(current_vertex) == 0) // using count, to find out whether vertex has been visited
     {
       visited.insert(current_vertex); // if not, then insert the vertex
       df_order.push_back(current_vertex); // put the vertex in the df_order
       
       for(auto n_it =graph.nbegin(current_vertex); n_it!= graph.nend(current_vertex); n_it++) // iterating through neighbour of current vertex
          unprocessed.push(*n_it); // push the neighbour to the unprocessed stack, to be processed
     }
  }
  return df_order; // after stack is empty, we return the depth first traversal order
}

/*
 * Computes the weakly connected components of the graph.
 * A [weak] component is the smallest subset of the vertices
 * such that the in and out neighbourhood of each vertex in
 * the set is also contained in the set.
 */
template <typename vertex>
vector<vector<vertex>> components(const directed_graph<vertex> & direct_graph) 
{
  directed_graph<vertex> graph(direct_graph); // copy graph
  vector<vector<vertex>> components; // 2d vector storing components for the graph
  unordered_set<vertex> visited; // unordered set, marking visit
  
/////////convert graph to undirected ///////// 
  for(auto v_it = graph.begin(); v_it!= graph.end(); v_it++)/////////vertex iterator to iterate through vertices in graph
  {
     vertex root = *v_it; //initialize  v_it to root
     if(graph.out_degree(root) > 0) // check if root has an out degree, meaning have neighbour
     {
         for(auto n_it = graph.nbegin(root); n_it!= graph.nend(root); n_it++) // iterate through root neighbour
         {
           if(!graph.adjacent(*n_it,root)) // checking if they are not adjacent
           graph.add_edge(*n_it, root); // switch the source and neighbour vertex, and add edge, this way
         }                              //graph will behave like undirected
     }
   }
/////////convert graph to undirected  //////////  
  
  for(auto v_it = graph.begin(); v_it!= graph.end(); v_it++)/////vertex iterator to iterate through vertices in graph
  {
      vertex root = *v_it; //initialize  v_it to root
      if(visited.count(root) == 0 ) // if root hasn't been visited
      {
        visited.insert(root); // mark root as visited
        auto component = depth_first(graph, root); // initialize new component from depth first

        for(auto current_vertex : component) // for each vertex in component
          if(visited.count(current_vertex)==0) // if they haven't been visited
            visited.insert(current_vertex); // mark them as visited
        
         components.push_back(component); // add the component to vectors of components
       } 
   }
  
    return components; // return the 2dvector containing all component in graph.
}

/*
 * Computes the strongly connected components of the graph.
 * A strongly connected component is a subset of the vertices
 * such that for every pair u, v of vertices in the subset,
 * v is reachable from u and u is reachable from v.
 */
template <typename vertex>
void tarjan(const directed_graph<vertex> &graph,  vector<vector<vertex>>& SCC, 
            unordered_map<vertex, bool>& stack_map, stack<vertex>& processed, 
            unordered_map<vertex, int>& low_map,   unordered_map<vertex, int>& index_map, 
              int & index, const vertex& start_vertex)

//employing tarjan algorithm to find strong_connected component in directed graph
// There's a couple of parameters here, all passed by reference!!!! to modify the data structure
// in the main method (STRONG CONNECT)
// only graph and startvertex are set to const, since the value won't be modified.
// however for SCC, stack_map, low_map, index_map, processed, index will have their value modified

{
  index_map[start_vertex] = index; // keep track of index count, num of vertex that has been visited
  low_map[start_vertex] = index; //keep track of the lowest node id reachable
  index++;
  
  processed.push(start_vertex); // push the vertex to the stack
  stack_map[start_vertex] = true; // mark vertex to be on stack
  
  for( auto n_it = graph.nbegin(start_vertex); n_it!=graph.nend(start_vertex); n_it++) // iterate through the vertex neighbour
  {
    auto neighbor = *n_it; // store iterator in neighbour
    if(index_map[neighbor] == numeric_limits<int>::max()) //if index map is undefined, in this case, if its the max value of int
    {
      tarjan(graph, SCC, stack_map, processed, low_map, index_map, index, neighbor); // recursive tarjan with neighbour
      low_map[start_vertex] = min(low_map[start_vertex],low_map[neighbor]);  // select min of low_map between root and neighbour
    }
    else if(stack_map[neighbor]) // if the stack is in neighbour
      low_map[start_vertex] = min(low_map[start_vertex],index_map[neighbor]); // select min of low_map of root, index_map neighbour
    
  }
  
  if(low_map[start_vertex] == index_map[start_vertex]) //if the low value of start vertex equal to index value of start vertex
  {
    vector<vertex> new_component;// store vector for new component
    vertex neighbor; // store neighbour vertex
    do
    {
      neighbor = processed.top(); // initialize top value of stack to neighbor
      processed.pop(); // remove the value from stack
      stack_map[neighbor] = false; // mark neighbor not on stack
      new_component.push_back(neighbor); // put neighbor to new component
    }while(neighbor!= start_vertex); // do this until neighbor is equal to start vertex; 
    
    SCC.push_back(new_component); // push the new component to vector of Strong connected components
  } 
}


template <typename vertex>
vector<vector<vertex>> strongly_connected_components(const directed_graph<vertex> & direct_graph) 
{
  directed_graph<vertex> graph(direct_graph); //copy graph
  vector<vector<vertex>> SCC; //strong connected component storing all SCC components in 2d vector
  unordered_map<vertex, bool> stack_map; // to mark whether, the vertex on stack or not
  stack<vertex> processed; //  stack to process the traversal
  unordered_map<vertex, int> low_map; // map each low value to each vertex
  unordered_map<vertex, int> index_map;// map each index value to each vertex
  int index = 0; // index counter
  
  for(auto v_it = graph.begin(); v_it!= graph.end(); v_it++) //iterating through graph using vertex_iterator
  {
      low_map.insert(pair<vertex, int>(*v_it, numeric_limits<int>::max())); 
      index_map.insert(pair<vertex, int>(*v_it, numeric_limits<int>::max())); 
      stack_map.insert(pair<vertex, bool>(*v_it, false));
      // initialize all vertex of low and index map  with maximum value of int (to mark undefined)
      // initialize stack map as well with false boolean value;
  }
  
  for(auto v_it = graph.begin(); v_it!= graph.end(); v_it++)//iterating through graph using vertex_iterator
  {
     vertex root = *v_it; // set vertex iterator value to root
     
    if(index_map[root] == numeric_limits<int>::max() ) // if index at root is undefined, hence not visited yet
      tarjan(graph, SCC, stack_map,  processed, low_map, index_map, index, root );// deploy tarjan algorithm  
  }
  
  return SCC; // return  components
   
}

/*
 * Computes the shortest distance from u to every other vertex
 * in the graph d. The shortest distance is the smallest number
 * of edges in any path from u to the other vertex.
 * If there is no path from u to a vertex, set the distance to
 * be the number of vertices in d plus 1.
 */

template <typename vertex>
unordered_map<vertex, size_t> shortest_distances(const directed_graph<vertex> & direct_graph, const vertex & start_vertex) 
{
    directed_graph<vertex> graph(direct_graph); // copy graph
    unordered_map<vertex, size_t> short_map; // short distances map mapping each vertex with their shortest distance
    unordered_set<vertex> visited; // markt whether vertex has been visited or not
    queue<vertex> unprocessed; // queue to process breadth first
    size_t count = 0; // counter to determine distance
  
    for(auto v_it = graph.begin(); v_it!= graph.end(); v_it++) // iterating through graph using vertex iterator
      short_map.insert(pair<vertex, int>(*v_it, -1)); // initialize map with each vertex, value -1
  
   unprocessed.push(start_vertex); // push start vertex to queue
   short_map[start_vertex] = 0; // make start vertex distance 0
   visited.insert(start_vertex); // make start vertex already visited
  
  while(!unprocessed.empty()) // while unprocessed is no empty
  {
    vertex current_vertex = unprocessed.front(); // store front value in current vertex
    unprocessed.pop(); // remove front value from queue
   
      for( auto n_it = graph.nbegin(current_vertex); n_it!= graph.nend(current_vertex); n_it++) // iterate through  current vertex neighbour
      {
        auto neighbor = *n_it; // store neighbour iterator in neighbor variable
         if(visited.count(neighbor) == 0) // if not visited
         {
            visited.insert(neighbor); // mark visited
            unprocessed.push(neighbor); // push neighbor to queue
            short_map[neighbor] = short_map.at(current_vertex) + 1; // increase distance by current vertex distance + 1
         }
      }  
   }
  
  for(auto v_it = graph.begin(); v_it!= graph.end(); v_it++) // iterate through graph
   if(visited.count(*v_it) == 0) // if any vertex not visited, means not reachable
     short_map[*v_it] = graph.num_vertices() + 1; // set their distance to num of vertices in graph + 1
   
  return short_map; //return map containing shortest distances
}


