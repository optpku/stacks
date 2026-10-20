/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.QuotientSheaf.Restriction
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 78.19.7: restricting a groupoid in algebraic spaces over `B` along
`g : U' ⟶ U` induces an injective map of fppf quotient sheaves `U'/R' ⟶ U/R`.
It is an isomorphism if the saturation morphism
`h = s ∘ pr₁ : U' ×_{g, U, t} R ⟶ U` is surjective as a map of fppf sheaves.
This holds in particular if the singleton family `{h}` is an fppf covering,
if `g` is surjective as a map of sheaves, or if `{g}` is an fppf covering. -/
@[stacks 044N] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.quotientSheafMap_isIso_of_saturationLocallySurjective :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (G.saturationMap g).left →
      IsIso (G.toPreRelation.quotientSheafMap g))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.quotientSheafMap_isIso_of_saturationCovering :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)
    [FppfCovering (fun _ : PUnit ↦ (Limits.pullback g G.t).left)
      (fun _ ↦ (G.saturationMap g).left)],
    IsIso (G.toPreRelation.quotientSheafMap g))

section

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
  (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafMap_isLocallyInjective
  G.toPreRelation g G.toPreRelation_isPreEquivalence :
  Sheaf.IsLocallyInjective (G.toPreRelation.quotientSheafMap g))

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafMap_isIso_of_locallySurjective
  G.toPreRelation g G.toPreRelation_isPreEquivalence :
  Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) g.left →
    IsIso (G.toPreRelation.quotientSheafMap g))

variable [FppfCovering (fun _ : PUnit ↦ U'.left) (fun _ ↦ g.left)]

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.quotientSheafMap_isIso_of_fppfCovering
  G.toPreRelation g G.toPreRelation_isPreEquivalence :
  IsIso (G.toPreRelation.quotientSheafMap g))

end
