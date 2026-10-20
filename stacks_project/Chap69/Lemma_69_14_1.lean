module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Decomposition
import StacksCheckRecall

/-!
# Lemma 69.14.1

A coherent module on a Noetherian algebraic space whose support is a union of two
closed subsets admits a short exact decomposition into coherent modules supported
on the respective subsets.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

/- Lemma 69.14.1: let `S` be a scheme, let `X` be a Noetherian algebraic space over `S`,
and let `F` be a coherent `𝒪_X`-module. If `moduleSupport F = Z ∪ Z'` for closed subsets
`Z`, `Z'` of `Points X`, then there is a short exact sequence `0 ⟶ G' ⟶ F ⟶ G ⟶ 0`
of coherent sheaves with `moduleSupport G' ⊆ Z'` and `moduleSupport G ⊆ Z`. -/
@[stacks 07UP] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.exists_shortExact_of_support_eq_union :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (Z Z' : TopologicalSpace.Closeds (Points X))
    (hSupp : moduleSupport F = (Z : Set (Points X)) ∪ (Z' : Set (Points X))),
    ∃ (G' G : X.Modules) (hG' : SheafOfModules.IsCoherent G')
      (hG : SheafOfModules.IsCoherent G)
      (ι : G' ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
      (hSuppG : moduleSupport G ⊆ (Z : Set (Points X))),
      (ShortComplex.mk ι π w).ShortExact ∧
        moduleSupport G' ⊆ (Z' : Set (Points X)))
