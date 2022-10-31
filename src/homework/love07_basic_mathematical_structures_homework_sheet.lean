import ..lectures.love12_basic_mathematical_structures_demo
import tactic

/-! # LoVe Homework 7: Basic Mathematical Structures (7 points)

Homework must be done individually.-/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

/-! ### Question 1 : Graph Definitions

There are many definitions of *graphs* in both the math and CS literature.
Graphs have *vertices* (or *nodes*) which are connected by *edges*.
Some definitions specify edges to be *directed*, i.e. 
an edge that connects vertex `a` to vertex `b` does not connect `b` to `a`.
Others are undirected.
Some allow *loops*, i.e. edges from a vertex `a` to itself. 
Some don't. 

A (undirected, loopless) graph is usually defined as a list of vertices
along with a list of tuples of vertices, representing edges:-/

structure list_graph (V : Type) :=
(edges : list (V × V))

/-! For large graphs, this data structure can get cumbersome. Instead, we
can define graphs based on an adjacency function. To ensure undirectedness
and looplessness, we need to prove our adjacency function is symmetric and
irreflexive, respectively. -/

structure func_graph (V : Type) :=
(adj : V → V → Prop)
(symm : symmetric adj)
(loopless : irreflexive adj )

/- 1.1 (3 points).
A complete graph is a graph in which each vertex is adjacent to each other vertex. 
Define the complete graph on four vertices, K₄, as a `list_graph` and as a `func_graph`.
You can use a predefined function for the adjacency function, or you can make your own! -/

inductive quad : Type
| one | two | three | four

namespace quad

def K₄' : list_graph quad := sorry

def K₄ : func_graph quad := sorry

end quad

/- 1.2 (4 points) 
If we choose the right type for a graph, it can be easier to define, manipulate, and manage
the graph. A `path graph` is a graph with vertices v₁,...,vₙ whose only edges are connecting
vᵢ and vᵢ₊₁ for i < n. Define a path graph `path₅` on the type `fin 5` by designing a symmetric 
and irreflexive function. You'll need to prove symmetry and irreflexivity, too!
-/
#check fin
/-
Be careful with addition on `fin`. You might recognize this type mathematically as `ℤ/5ℤ`.
-/
#eval (4 : fin 5) + 1
/-
You also might be surprised that tactics like `linarith` don't work on `fin 5`. 
Turns out that algorithm doesn't like it when `5 = 0`!
If you end up with a hypothesis `h : 0 = 1` or something like that,
`cases h` may come in handy.
-/

def path₅ : func_graph (fin 5) := sorry

/- 1.3 (1 point)
Using this functional definition of a graph, we can easily generalize the above path graph
to make an arbitrarily large path. Fill in the following definition, utilizing your previous
answer. -/

def pathBIG : func_graph (fin 100) := sorry

/- Extra Challenge: define `pathBig` as a list_graph. (just kidding don't do that)-/


/- 1.4 (Bonus)
We lied a bit: the definitions `func_graph` and `list_graph` are actually capturing 
slightly different graph concepts!

To make that more precise: we can state the *equivalence* of a `list_graph` and a `func_graph`. 
-/
def graph_equiv {α : Type} (lg : list_graph α) (fg : func_graph α) : Prop :=
∀ v₁ v₂ : α, fg.adj v₁ v₂ ↔ ((v₁, v₂) ∈ lg.edges ∨ (v₂, v₁) ∈ lg.edges)

/-
I claim that I can find two non-equal `func_graphs` that are equivalent to the same `list_graph`.

Can you give an example? What graph theory concept is appearing here?
-/



/- For question 2, you may chose to do **one** of Question 2α or Question 2β. You may do both,
but you will only be graded for one. Please indicate which one you want to be graded.
Question 2α will be more in the realm of math and logic.
Question 2β will be more about CS, PL, and functional programming. -/

/- ### Question 2α : Automorphism Groups of Graphs (6 points) -/
/- An automorphism of a graph is a function on (or permutation of) its vertices that preserves
the edge structure of the graph. In other words: -/
def is_graph_automorphism {α : Type} (G : func_graph α) (A : α → α) : Prop :=
  ∀(v₁ v₂ : α), G.adj v₁ v₂ ↔ G.adj (A v₁) (A v₂)

/- We can define a structure like this to define an automorphism of a graph. -/
structure graph_automorphism (α : Type) (G : func_graph α) :=
(f : α → α)
(is_aut : is_graph_automorphism G f)


/- Let's focus on a particular graph, say, the graph `path₅` defined above, to define and study
its automorphisms. It has two automorphisms: the identity, which fixes all vertices, and a 'flip',
which fixes the middle vertex, maps terminal vertices to terminal vertices, and the two remaining
vertices to each other. -/

/- 2α.1 (1 point)
Define the two functions corresponding to the `flip` and the `identity` on the `path₅` graph.
-/

def path₅_flip : fin 5 → fin 5 := sorry

def path₅_id : fin 5 → fin 5 := sorry

/- 2α.2 (1 point)
Now prove that these functions are indeed automorphisms.
-/

lemma path₅_flip_is_aut : is_graph_automorphism path₅ path₅_flip := sorry

lemma path₅_id_is_aut : is_graph_automorphism path₅ path₅_id := sorry

/- Now we can define the two elements of our structure! -/
def path₅_flip_aut : graph_automorphism (fin 5) path₅ :=
{
  f := path₅_flip,
  is_aut := path₅_flip_is_aut
}

def path₅_id_aut : graph_automorphism (fin 5) path₅ :=
{
  f := path₅_id,
  is_aut := path₅_id_is_aut
}

/- Graph automorphisms under the operation of function composition form a group! Let's work 
towards building that group for our path₅ graph.
-/

/- Question 2α.3 (2 points) 
First, let's prove that automorphisms are closed under composition (`aut_comp_aut`).
Then we'll define the composition function as `aut_comp`. 

Hint for the lemma: `iff.trans` might be handy!
-/

lemma aut_comp_aut {α : Type} (G : func_graph α) (f g : α → α) :
  is_graph_automorphism G f → is_graph_automorphism G g → is_graph_automorphism G (f ∘ g) :=
sorry


def aut_comp {α : Type} (G : func_graph α) :
 graph_automorphism α G → graph_automorphism α G → graph_automorphism α G := sorry

infix ` ∘₅ ` : 90 := aut_comp path₅

/- Question 2α.4 (2 points) 
Now prove that this operation is associative and define an inverse function. (Note that the
inverse function is defined only on the path₅ graph, so don't overthink it! What are the inverses
of each element?) -/

lemma graph_automorphism.assoc : 
  ∀ (a b c : graph_automorphism (fin 5) path₅), a ∘₅ b ∘₅ c = a ∘₅ (b ∘₅ c) := sorry

def graph_automorphism.inv : graph_automorphism (fin 5) path₅ → graph_automorphism (fin 5) path₅ := sorry

/- You don't have to prove the rest, but if you did, you'd have a group! Notice also how easy it would
be to generalize this group to an automorphism group of any path graph. -/

axiom graph_automorphism.one_mul : ∀ (a : graph_automorphism (fin 5) path₅), path₅_id_aut ∘₅ a = a
axiom graph_automorphism.mul_one : ∀ (a : graph_automorphism (fin 5) path₅), a ∘₅ path₅_id_aut = a
axiom graph_automorphism.mul_left_inv : ∀ (a : graph_automorphism (fin 5) path₅), graph_automorphism.inv a ∘₅ a = path₅_id_aut

@[instance] def automorphism_group_path₅ : group (graph_automorphism (fin 5) path₅) :=
{
  mul := aut_comp path₅,
  one := path₅_id_aut,
  mul_assoc := graph_automorphism.assoc,
  one_mul := graph_automorphism.one_mul,
  inv := graph_automorphism.inv,
  mul_one := graph_automorphism.mul_one,
  mul_left_inv := graph_automorphism.mul_left_inv,
}

/- ### Question 2β : Computer Networks (6 points)-/
/- Computer networks can be modeled by graphs. Suppose we have a system of routers, and
we want any router to be able to send and receive information from any other router. Graph
theoretically, we want our graph to be connected.
-/

/- Question 2β.1 (2 points)
We'll say a path is valid if it
* Starts with the starting vertex `start_v`
* Ends with the ending vertex `end_v`
* For each element in the list vᵢ, vᵢ₊₁ is adjacent to vᵢ

Fill in the predicate `is_path` that holds when an input list is a valid path.
-/

def is_path {α : Type} (G : func_graph α) (start_v end_v: α) : list α → Prop := sorry

def is_connected {α : Type} (G : func_graph α) : Prop :=
  ∀(v₁ v₂ : α), v₁ ≠ v₂ → ∃p, is_path G v₁ v₂ p

/- Suppose now that Ian, infamous for hating routers, destroys one of the routers. It's very
much possible that the destruction of that router disconnected the rest of the network, i.e., after that
router is destroyed, there are some routers that can no longer communicate with others. We would
call that router a **separation vertex**. We might consider employing the stricter condition of
**biconnectivity** to avoid this problem. Biconnectivity is when there are no separation vertices
in the graph, or, alternatively, for every two vertices there are two disjoint paths connecting them. -/

/- Question 2β.2 (1 point) 
Write an inductive predicate that holds when two lists are totally disjoint (their intersection is empty). -/

inductive list_disj {α : Type} : list α → list α → Prop

/- Question 2β.3 (1 point)
Use the predicate above to write a definition for biconnectivity. -/

def is_biconnected {α : Type} (G : func_graph α) : Prop := sorry

/-  Question 2β.4 (2 points)

Define a biconnected graph of your choice (with at least 4 vertices) and prove that it is biconnected!
-/

def bcgraph : func_graph sorry := sorry 

lemma bc_graph_is_biconnected : is_biconnected bcgraph :=
sorry

end LoVe
