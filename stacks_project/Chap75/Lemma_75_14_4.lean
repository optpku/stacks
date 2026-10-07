module

public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap75.Definition_75_3_2_SupportedOn
public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_3_1_Restrict

/-!
# Perfect approximation along an elementary distinguished square

On an elementary distinguished square, a perfect approximation of the restricted
triple on `V` extends to `X` when the closed support lies in `|X| \ |U|` and the
cohomology sheaves of `E` from degree `m` onward are supported on that closed set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Restriction of modules along an étale morphism of algebraic spaces is additive. -/
instance restrictFunctor.instAdditive {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] : (restrictFunctor f).Additive :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The restriction `E|_V` of an object of `DerivedQCoh X` along an étale morphism
`f : V ⟶ X`, as an object of `DerivedQCoh V`. -/
def restrict {S : Scheme.{u}} {V X : AlgebraicSpace S} (f : V ⟶ X) [Etale f]
    (E : DerivedQCoh X) : DerivedQCoh V where
  obj := (restrictFunctorDerived f).obj E.obj
  property := sorry

/-- The underlying derived module of étale restriction is derived étale restriction of
the underlying module. -/
theorem restrict_obj {S : Scheme.{u}} {V X : AlgebraicSpace S} (f : V ⟶ X) [Etale f]
    (E : DerivedQCoh X) :
    (restrict f E).obj = (restrictFunctorDerived f).obj E.obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

namespace AlgebraicGeometry.AlgebraicSpace.HasPerfectApproximation

/-- Lemma 75.14.4: let `S` be a scheme and let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Let `T` be a closed subset of
`|X| \ |U|` and let `(T, E, m)` be a triple as in `HasPerfectApproximation`. If
approximation holds for `(f⁻¹T, E|_V, m)`, and the sheaves `H^i(E)` for `m ≤ i` are
supported on `T`, then approximation holds for `(T, E, m)`. The source morphism
`j : V → X` is this étale map `f`, and `j⁻¹T` is `T.preimage (Points.continuous_map f)`. -/
@[stacks 08HL]
theorem of_isElementaryDistinguishedSquare
    {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
    [Etale f] [IsElementaryDistinguishedSquare j f] (T : Closeds (Points X))
    (hT : (T : Set (Points X)) ⊆ (toOpenSubspace j f).pointsSetᶜ) (E : DerivedQCoh X)
    (m : ℤ)
    (hV : HasPerfectApproximation (T.preimage (Points.continuous_map f))
      (DerivedQCoh.restrict f E) m)
    (hE : ∀ i : ℤ, m ≤ i →
      Modules.moduleSupportedOn (T : Set (Points X))
        ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj)) :
    HasPerfectApproximation T E m :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.HasPerfectApproximation
