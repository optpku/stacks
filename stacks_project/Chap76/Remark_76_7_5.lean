/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap76.Lemma_76_7_6_Comparison
public import stacks_project.Chap76.Remark_76_7_5_Glueing

/-!
# Alternative constructions of the sheaf of differentials

Remark 76.7.5 records three elementary glueing presentations of the sheaf of
relative differentials of a morphism of algebraic spaces. Each recovers the
canonical sheaf Ω[f] on X.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Differentials
open AlgebraicGeometry.AlgebraicSpace.QCoh
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

/-- Remark 76.7.5 (1): If `Y` is a scheme and `φ : U ⟶ X` is a surjective étale morphism
from a scheme, the sheaf `Ω_{U/Y}` is a quasi-coherent `𝒪_U`-module. Since `s, t : R ⟶ U`
are étale, Morphisms Lemma 29.34.16 supplies an isomorphism
`α : s* Ω_{U/Y} ⟶ Ω_{R/Y} ⟶ t* Ω_{U/Y}` equal to `sourceComparison ≫ inv targetComparison`
after identifying the two presentations of `Ω_{R/Y}` along the kernel pair of `φ`.
After the cocycle condition, glueing via Properties of Spaces Section 66.32 produces the
canonical sheaf `Ω[f]` on `X`. -/
@[stacks 04CW]
theorem glued_isIsomorphic_relativeDifferentials {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U Y : Over S} (f : X ⟶ ofOver Y) (φ : ofOver U ⟶ X)
    [Etale φ] [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ] :
    IsIsomorphic ((inclusion X).obj (glued f φ)) (relativeDifferentials f) :=
  sorry

/-- Remark 76.7.5 (2): If `Y` is not a scheme, define `Ω_{U/Y}` as the cokernel of
`(U ⟶ Y)* Ω_{Y/S} ⟶ Ω_{U/S}` and glue as in (1). The resulting sheaf on `X` is the
canonical sheaf `Ω[f]`. -/
@[stacks 04CW]
theorem cokerGlued_isIsomorphic_relativeDifferentials {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U : Over S} (f : X ⟶ Y) (φ : ofOver U ⟶ X)
    [Etale φ] [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ] :
    IsIsomorphic ((inclusion X).obj (cokerGlued f φ)) (relativeDifferentials f) :=
  sorry

/-- Remark 76.7.5 (3): Glueing the sheaves `Ω_{U/V}` for diagrams as in Lemma 76.7.3,
with étale vertical arrows and surjective `a : U ⟶ X`, produces the canonical sheaf
`Ω[f]` on `X`. -/
@[stacks 04CW]
theorem diagramGlued_isIsomorphic_relativeDifferentials {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U V : Over S} (f : X ⟶ Y) (ψ : U ⟶ V)
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) [Etale a] [Etale b]
    (sq : CommSq a (ofOverMap ψ) f b)
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a] :
    IsIsomorphic ((inclusion X).obj (diagramGlued f ψ a b sq)) (relativeDifferentials f) :=
  sorry

end Differentials
end Hom
end AlgebraicSpace
end AlgebraicGeometry
