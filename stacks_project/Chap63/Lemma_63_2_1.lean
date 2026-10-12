/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SupportExcision
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

open AlgebraicGeometry.Scheme.Etale

/- Lemma 63.2.1: an étale-site morphism identifying a closed subscheme with a
closed image induces a canonical bijection of the corresponding supported
sections. The comparison is restriction when the inverse-image support equals
the original closed image. -/
@[stacks 0F6F] #check (AlgebraicGeometry.Scheme.Etale.abelianSheafSectionsSupportedInAddEquiv :
  ∀ {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {U U' : X.Etale} (φ : U' ⟶ U) {Z' : Scheme.{u}} (ι : Z' ⟶ U'.left)
    [IsClosedImmersion ι] [IsClosedImmersion (ι ≫ φ.left)],
    abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left)) ≃+
      abelianSheafSectionsSupportedIn F U' (Set.range ι))

#check (AlgebraicGeometry.Scheme.Etale.abelianSheafSectionsSupportedInAddEquiv_apply_of_preimage_eq :
  ∀ {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {U U' : X.Etale} (φ : U' ⟶ U) {Z' : Scheme.{u}} (ι : Z' ⟶ U'.left)
    [IsClosedImmersion ι] [IsClosedImmersion (ι ≫ φ.left)]
    (h_preimage : φ.left ⁻¹' Set.range (ι ≫ φ.left) = Set.range ι)
    (σ : abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left))),
    (abelianSheafSectionsSupportedInAddEquiv F φ ι σ).val = F.1.map φ.op σ.val)
