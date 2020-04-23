theory Chapter3
  imports Chapter2 "HOL-Algebra.Sym_Groups" "HOL-Algebra.Group_Action"
begin
section\<open>Digression on Groups and Automorphisms\<close>
text \<open>
\begin{hartshorne}
\defn[group]. A \term{group} is a set $G$ together with a binary operation, called multiplication,
written $ab$ such that
\begin{itemize}
\item[G1] (\term{Associativity}) For all $a,b,c\in G, (ab)c = a(bc)$.
\item[G2] There exists an element $1 \in G$ such that $a \cdot 1 = 1 \cdot a = a \cdot 1 = a$ for all $a$.
\item[G3] For each $a \in G$, there exists an element $a^{-1} \in G$ such that $aa^{-1} = a^{-1}a = 1$.
\end{itemize}
The element $1$ is called the \term{identity}, or \term{unit}, element. The element $a^{-1}$ is 
called the \term{inverse} of $a.$ Note that in general the product $ab$ may be different from $ba.$
However, we say that the group $G$ is \term{abelian,} or \term{commutative,} if
G4 $\forall a, b \in G, ab = ba.$
\end{hartshorne}
\<close>

text \<open>
\begin{hartshorne}
Examples. 

1. Let $S$ be any set, and let $G$ be the set of permutations of the set $S.$
A \term{permutation} is a 1–1 mapping of a set $S$ onto $S.$ If $g_1, g_2 \in G$
are two permutations, we define $g_1 g_2 \in G$ to be the permutation obtained by 
performing first $g_2$, then $g_1$, i.e., if $x \in S$, then
$$
(g_1g_2)(x) = g_1(g_2(x)).
$$

2. Let $C$ be a configuration, and let $G$ be the set of \term{automorphisms} of $C$,
i.e., the set of those permutations of $C$ which send lines into lines. 
Again we define the product $g_1g_2$ of two automorphisms $g_1,g_2$, by performing 
$g_2$ first, and then $g_1.$ This group is written $\operatorname{Aut} C$.

\defn [homomorphism] A \term{homomorphism} $\phi: G_1 \to G_2$ of one group to another is a 
mapping of the set $G_1$ to the set $G_2$ such that $\phi(ab) = \phi(a) \phi(b)$ for each $a, b \in G_1$. 

An \term{isomorphism} of one group with another is a homomorphism which is
1–1 and onto.

\defn [subgroup]  Let $G$ be a group. A subgroup of $G$ is a non-empty subset
$H \subseteq G,$ such that for any $a,b \in H,$ $ab \in H$ and $a^{-1} \in H.$
\end{hartshorne}
 \<close>





subsection\<open>Automorphisms of the real projective plane\<close>
text \<open>\begin{hartshorne}Here we study another important example of the automorphisms of a pro-
jective plane. Recall that the real projective plane is defined as follows: A point
is given by homogeneous coordinates $(x_1 , x_2 , x_3 )$. That is, a triple of real num-
bers, not all zero, and with the convention that $(x_1 , x_2 , x_3)$ and $(\lambda x_1, \lambda x_2, \lambda x_3)$
represent the same point, for any $\lambda \ne 0$, $\lambda \in \Bbb R.$ 
A \term{line} is the set of points which satisfy an equation of the form 

\begin{equation*}
a_1 x_1 + a_2 x_2 + a_3 x_3 = 0,
\end{equation*}

$a_i \in \Bbb R,$ not all zero. \end{hartshorne}\<close>

subsubsection\<open>Brief review of matrices\<close>
text \<open>\begin{hartshorne}
A $n \times n$ \term{matrix} of real numbers is a collection of $n^2$ real numbers, indexed
by two indices, say $i$, $j$, each of which may take values from 1 to $n$. Hence
$A = {a_{11}, a_{12}, \ldots , a_{21}, a_{22}, \ldots , a_{n1}, a_{n2}, \ldots , a_{nn}}.$ The matrix is
usually written in a square:
$$
\begin{pmatrix}
a_{11} & a_{12} & \hdots & a_{1n} \\
a_{21} & a_{22} & \hdots & a_{2n} \\
\vdots & \vdots & \ddots & \vdots \\
a_{n1} & a_{n2} & \hdots & a_{nn}
\end{pmatrix} 
$$
Here the first subscript determines the row, and the second subscript determines
the column.

The product of two matrices $A = (a_{ij})$ and $B = (b_{ij})$ (both of order $n$) is
defined to be

\begin{equation*}
  A \cdot B = C
\end{equation*}

where $C = (c_{ij})$ and

\begin{equation*}
  c_{ij} = \sum_{k=1}^n a_{ik} b_{kj}.
\end{equation*}

\[
\begin{pmatrix}
a_{i1} & \hdots & a_{in} \\
\end{pmatrix}
\begin{pmatrix}
b_{1j} \\
\vdots \\
b_{nj} \\
\end{pmatrix}
= ( c_{ij} )
\]


\[c_{ij} = a_{i1}b_{1j} + a_{i2}b_{2j} + \hdots  + a_{in}b_{nj}\]

There is also a function \textbf{determinant}, from the set of $n \times n$ matrices to $\mathbb{R}$,
which is characterized by the following two properties:

\textbf{D1} \textit{If A, B are two matrices}

\[ det(A \cdot B) = det A \cdot det B\]

\textbf{D2} \textit{For each $a \in R$, let $C(a) = \ldots $}

Note incidentally that the identity matrix $I = C(1)$ behaves as a multiplicative identity. 
One can prove the following facts:
\begin{enumerate}
\item $(A \cdot B) \cdot C = A \cdot (B \cdot C)$, i.e. multiplication of matrices is associative. 
(In general it is not commutative.)

\item A matrix $A$ has a multiplicative inverse $A^{-1}$
if and only if $det A \neq 0$.

Hence the set of $n \times n$ matrices $A$ with $\det A \neq 0$ forms a group under multiplication, 
denoted by GL$(n, \mathbb{R})$. 
\item Let $A = (a_{ij})$ be a matrix, and consider the set of simultaneous linear
equations
\begin{align}
a_{11}x_1 + a_{12}x_2 + \hdots + a_{1n}x_n &= b_1 \\
a_{21}x_1 + a_{22}x_2 + \hdots + a_{2n}x_n &= b_2 \\
\vdots &= \vdots\\
a_{n1}x_1 + a_{n2}x_2 + \hdots + a_{nn}x_n &= b_n
\end{align}
If $\det A \neq 0$, then this set of equations has a solution. Conversely, if this
set of equations has a solution for all possible choices of $b_1, \hdots, b_n$ then
$\det A \neq 0$.
\end{enumerate}
For proofs of these statements, refer to any book on algebra. We will take
them for granted, and use them without comment in the rest of the course. One
can prove easily that 3 follows from 1 and 2. Because to say $x_1, \hdots, x_n$ are a
solution of that system of linear equations is the same as saying that

\[
A \cdot
\begin{pmatrix}
x_1 \\
x_2 \\
\vdots \\
x_n \\
\end{pmatrix}
=
\begin{pmatrix}
b_1 \\
b_2 \\
\vdots \\
b_n \\
\end{pmatrix}
\]
Now let $A = (a_{ij})$ be a $3 \times 3$ matrix of real numbers, and let $\pi$ be the real
projective plane, with homogeneous coordinates $x_1, x_2, x_3$. We define a transformation $T_A$ of $\pi$ as follows: 
The point $(x_1, x_2, x_3)$ goes into the point
\[T_A(x_1, x_2, x_3) = (x_1', x_2', x_3')\]
where
\[x_1' = a_{11}x_1 + a_{12}x_2 + a_{13}x_3\]
\[x_2' = a_{21}x_1 + a_{22}x_2 + a_{23}x_3\]
\[x_3' = a_{31}x_1 + a_{32}x_2 + a_{33}x_3\]
\end{hartshorne}
\<close>

(*
CONTINUES WITH DOT-PRODUCT DEFINITION OF MATRIX MULTIPLICATION
*)

(*
(* Proposition 3.1: There is a 1-1 correspondence between the elements
 of H, a subgroup of G, and the elements of gH. *)

(* Some definitions that make the statement of 3.1 easier. *)
definition injective :: "('a  \<Rightarrow> 'b) \<Rightarrow> ('a set) \<Rightarrow> ('b set)  \<Rightarrow> bool"
  where "injective f U V  \<longleftrightarrow> (\<forall> u1 \<in> U. \<forall> u2 \<in> U. (f(u1) = f(u2)) \<longleftrightarrow> (u1 = u2))" 

definition surjective :: "('a  \<Rightarrow> 'b) \<Rightarrow> ('a set) \<Rightarrow> ('b set) \<Rightarrow> bool"
  where "surjective f U V  \<longleftrightarrow>  (\<forall> v \<in> V. \<exists>u \<in> U. f(u) = v)"

definition bijective :: "('a  \<Rightarrow> 'b) \<Rightarrow> ('a set) \<Rightarrow> ('b set)  \<Rightarrow> bool"
  where "bijective f U V \<longleftrightarrow> (injective f U V \<and> surjective f U V)"

(* A map is homomorphic if it preserves the structure of the objects it maps between.
 * I.e., if it preserves the behavior of the operators A and B. *)
definition homomorphic :: "('a  \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a  \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b  \<Rightarrow> 'b) \<Rightarrow> bool"
  where "homomorphic f A B \<longleftrightarrow> ( \<forall> a b. (f(A a b) = B (f(a)) (f(b))))"
*)


(*
lemma bijection_btw_left_cosets:
  assumes "group G"
  assumes "g \<in> carrier G"
  assumes "subgroup H G"
  assumes "gH = H <#\<^bsub>G\<^esub> g"
  shows "\<exists>f. bij_betw f H gH"
proof -
  have "gH \<in> lcosets\<^bsub>G\<^esub> H" sorry
  thus thesis? sorry
qed
*)

lemma group_action_is_group:
  assumes "group_action G E phi"
  shows "group G"
  using assms group_action.group_hom group_hom.axioms(1) by blast

lemma bij_group_action:
  assumes "G = BijGroup S"
  shows "group_action G S (\<lambda>g e. g(e))"
  by (simp add: assms group_BijGroup group_action.intro group_hom.intro group_hom_axioms.intro homI)

text\<open>Example\<close>
lemma bij_fix_el_are_subgroup:
  assumes "G = BijGroup S"
  assumes "x \<in> S"
  assumes "H = stabilizer G (\<lambda>g e. g(e)) x" 
  shows "subgroup H G"
  using assms(1) assms(2) assms(3) bijections_are_a_group_action group_action.stabilizer_subgroup by fastforce

text\<open>Proposition 3.1 (but with right cosets)\<close>
lemma bij_btw_right_cosets:
  assumes "group G"
  assumes "g \<in> carrier G"
  assumes "subgroup H G"
  assumes "Hg = H #>\<^bsub>G\<^esub> g"
  shows "\<exists>f. bij_betw f H Hg"
proof -
  have "Hg \<in> rcosets\<^bsub>G\<^esub> H"
    by (simp add: assms(1) assms(2) assms(3) assms(4) group.rcosetsI group.subgroupE(1))
  thus ?thesis
    using assms(1) assms(3) group.card_cosets_equal subgroup.subset by blast
qed

text\<open>Corollary 3.2\<close>
lemma lagrange_group_card:
  assumes "group G"
  assumes "subgroup H G"
  shows "card(carrier G) = card(H) * card(rcosets\<^bsub>G\<^esub> H)"
  by (metis assms(1) assms(2) group.lagrange order_def semiring_normalization_rules(7))

text\<open>Example\<close>
lemma orbit_stabilizer_thm:
  assumes "G = BijGroup S"
  assumes "phi = (\<lambda>g e. g(e))"
  assumes "x \<in> S"
  assumes "H = stabilizer G phi x"
  shows "card(carrier G) = card(H) * card(orbit G phi x)"
proof -
  have "group_action G S phi"
      by (simp add: assms(1) assms(2) bij_group_action)
    thus ?thesis 
      by (metis assms(3) assms(4) group_action.orbit_stabilizer_theorem mult.commute order_def)
qed


text\<open>Example above, in transitive group\<close>
lemma trans_orbit_stabilizer_thm:
  assumes "subgroup G_car (BijGroup S)"
  assumes "G = \<lparr>carrier = G_car, mult = mult (BijGroup S), one = one (BijGroup S)\<rparr>"
  assumes "phi = (\<lambda>g e. g(e))"
  assumes "transitive_action G S phi"
  assumes "x \<in> S"
  assumes "H = stabilizer G phi x"
  shows "card(carrier G) = card(H) * card(S)"
proof -
  have "card(carrier G) = card(H) * card(orbit G phi x)"
    by (metis assms(4) assms(5) assms(6) group_action.orbit_stabilizer_theorem linordered_field_class.sign_simps(5) order_def transitive_action.axioms(1))
  also have "S = orbit G phi x"
  proof 
    show "S \<subseteq> orbit G phi x"
      by (smt CollectI assms(4) assms(5) orbit_def subsetI transitive_action.unique_orbit)
    show "orbit G phi x \<subseteq> S"
      by (smt assms(4) assms(5) group_action.element_image mem_Collect_eq orbit_def subsetI transitive_action.axioms(1))
  qed
  then have cards_same: "card S = card (orbit G phi x)"
    by simp
  thus ?thesis
    by (simp add: calculation)
qed



(*
theorem bijection_between_cosets:
  assumes G_is_a_group: "group G" 
  assumes H_subgroup_G: "subgroup H G"
  assumes gH_coset: "gH \<in> l_cosets H"
  shows "\<exists>f. bijective f H gH"
proof -
  obtain g where g: "(g \<in> carrier G) \<and> (gH = (g <# H))" try
 (* obtain f where "f h = g \<otimes> h" *)
qed
*)

end





