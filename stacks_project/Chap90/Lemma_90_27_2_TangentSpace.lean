module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Definition_90_27_1
public import stacks_project.Chap90.Example_90_16_10
public import stacks_project.Chap90.Theorem_90_18_2_OfDerivation

/-!
# Tangent map of the quotient morphism `U ⟶ [U/R]`

For a smooth prorepresentable groupoid in functors, the quotient projection
`[U/R] ⟶ C_Λ` is a deformation category. The induced comparison
`TU → T[U/R]` sends a dual-number object of `U` to the isomorphism class of the
corresponding Grothendieck object `(k[ε], x)` in the dual-number fibre of `[U/R]`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open Functor Fiber

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- A smooth prorepresentable groupoid in functors has quotient projection `[U/R] ⟶ C_Λ`
a deformation category. -/
instance instIsDeformationCategory_forget
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :
    Functor.IsDeformationCategory G.forget := sorry

/-- The tangent space `T[U/R]` is the type of isomorphism classes of objects in the
fibre of `G.forget` over `dualNumber Λ k`. -/
abbrev quotientTangentSpace
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :=
  isomorphismClasses.obj (Cat.of (G.forget.Fiber (dualNumber Λ k)))

/-- `quotientTangentSpace G` is the type of isomorphism classes of the dual-number
fibre of `[U/R]`. -/
theorem quotientTangentSpace_def
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :
    quotientTangentSpace G =
      isomorphismClasses.obj (Cat.of (G.forget.Fiber (dualNumber Λ k))) := sorry

/-- The dual-number fibre object of `[U/R]` associated to a point of `U(k[ε])`. -/
def quotientTangentSpaceFiber
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G]
    (x : IsPredeformationFunctor.tangentSpace G.U) :
    G.forget.Fiber (dualNumber Λ k) :=
  Fiber.mk (G.forget_obj (dualNumber Λ k) x)

/-- The fibre object associated to `x` lies over `dualNumber Λ k`. -/
theorem quotientTangentSpaceFiber_over
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G]
    (x : IsPredeformationFunctor.tangentSpace G.U) :
    G.forget.obj (fiberInclusion.obj (quotientTangentSpaceFiber G x)) =
      dualNumber Λ k := sorry

/-- The comparison map `TU → T[U/R]` induced by the quotient morphism `U ⟶ [U/R]`. -/
def quotientTangentSpaceMap
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G]
    (x : IsPredeformationFunctor.tangentSpace G.U) :
    quotientTangentSpace G :=
  Quotient.mk'' (quotientTangentSpaceFiber G x)

/-- `quotientTangentSpaceMap G x` is the isomorphism class of the dual-number fibre
object associated to `x`. -/
theorem quotientTangentSpaceMap_apply
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G]
    (x : IsPredeformationFunctor.tangentSpace G.U) :
    quotientTangentSpaceMap G x = Quotient.mk'' (quotientTangentSpaceFiber G x) := sorry

/-- The origin of `TU`, obtained by pushing the unique residue value along
`residueToDualNumber`. -/
def originTangentSpace
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :
    IsPredeformationFunctor.tangentSpace G.U :=
  G.U.map (residueToDualNumber Λ k) (IsPredeformationFunctor.residuePoint G.U)

/-- The origin of `TU` is the image of `residuePoint G.U` under `U.map residueToDualNumber`. -/
theorem originTangentSpace_apply
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :
    originTangentSpace G =
      G.U.map (residueToDualNumber Λ k) (IsPredeformationFunctor.residuePoint G.U) := sorry

/-- Zero on `T[U/R]`, as the image of the origin of `TU`. -/
instance instZero_quotientTangentSpace
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :
    Zero (quotientTangentSpace G) where
  zero := quotientTangentSpaceMap G (originTangentSpace G)

/-- The zero tangent vector of `[U/R]` is the class of the origin of `U`. -/
theorem quotientTangentSpace_zero
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] :
    (0 : quotientTangentSpace G) = quotientTangentSpaceMap G (originTangentSpace G) := sorry

end CategoryTheory.GroupoidInFunctors
