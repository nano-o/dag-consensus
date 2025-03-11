----------------------------- MODULE Digraph -----------------------------

\* A digraph is a pair consisting of a set of vertices and a set of edges
Vertices(digraph) == digraph[1]
Edges(digraph) == digraph[2]

IsDigraph(digraph) ==
    /\  digraph = <<Vertices(digraph), Edges(digraph)>>
    /\  \A e \in Edges(digraph) :
        /\  e = <<e[1],e[2]>>
        /\  {e[1],e[2]} \subseteq Vertices(digraph)

Children(v, digraph) ==
    {c \in Vertices(digraph) : <<v,c>> \in Edges(digraph)}

RECURSIVE Reachable(_,_,_)
Reachable(v1, v2, dag) ==
    \/  v1 = v2
    \/  \E c \in Children(v1, dag) : Reachable(c, v2, dag)

RECURSIVE Descendants(_, _) \* union of reachable
Descendants(vs, dag) == IF vs = {} THEN {} ELSE
    LET children == {c \in Vertices(dag) : \E v \in vs : <<v,c>> \in Edges(dag)} IN
        children \cup Descendants(children, dag)

Parents(v, digraph) ==
    LET incomingEdges == {e \in Edges(digraph) : e[2] = v}
    IN  {e[1] : e \in incomingEdges}

==========================================================================
