module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import stacks_project.Chap36.Lemma_36_4_1
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap75.Lemma_75_4_2_Pullback
public import stacks_project.Chap75.Lemma_75_5_5
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward

/-!
# Matching derived pullback and pushforward for representable algebraic spaces

A morphism of representable algebraic spaces over `S` is represented by a morphism
of schemes `f0 : X0 ⟶ Y0`. Lemma 75.4.2 identifies `D_QCoh(𝒪_{X0})` with
`D_QCoh(𝒪_X)` via `ε*` along the flat morphism of ringed sites from the small
étale site of `ofOver X0` to the Zariski site of `X0.left`, and likewise for `Y`.
Derived pullback always commutes with these identifications; if `f0` is
quasi-compact and quasi-separated, equivalently if `ofOverMap f0` is, derived
pushforward commutes as well.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.Scheme.DerivedQCoh (SmallEtale)
open CategoryTheory.ObjectProperty
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of representable algebraic spaces over `S` is quasi-compact if and only
if the representing morphism of schemes is quasi-compact. -/
theorem quasiCompact_ofOverMap_iff {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    QuasiCompact (ofOverMap f0) ↔ AlgebraicGeometry.QuasiCompact f0.left :=
  sorry

/-- Quasi-compactness of `ofOverMap f0` yields quasi-compactness of `f0.left`. -/
instance instQuasiCompact_left_ofOverMap {S : Scheme.{u}} {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) [QuasiCompact (ofOverMap f0)] :
    AlgebraicGeometry.QuasiCompact f0.left :=
  sorry

/-- A morphism of representable algebraic spaces over `S` is quasi-separated if and only
if the representing morphism of schemes is quasi-separated. -/
theorem quasiSeparated_ofOverMap_iff {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    QuasiSeparated (ofOverMap f0) ↔ AlgebraicGeometry.QuasiSeparated f0.left :=
  sorry

/-- Quasi-separatedness of `ofOverMap f0` yields quasi-separatedness of `f0.left`. -/
instance instQuasiSeparated_left_ofOverMap {S : Scheme.{u}} {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) [QuasiSeparated (ofOverMap f0)] :
    AlgebraicGeometry.QuasiSeparated f0.left :=
  sorry

/-- Module pushforward along `schemeEtaleRingedHom U` admits its inverse-image left
adjoint. -/
instance instIsRightAdjoint_schemeEtaleRingedHom_modulePushforward
    {S : Scheme.{u}} (U : Over S) :
    ((schemeEtaleRingedHom U).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- The ringed-site identification of the small étale site of `ofOver U` with the small
étale site of `U.left` is flat. -/
instance instIsFlat_schemeEtaleRingedHom {S : Scheme.{u}} (U : Over S) :
    IsFlat.{u} (schemeEtaleRingedHom U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- Derived pullback `Lf^*` along a morphism of algebraic spaces, restricted to complexes
with quasi-coherent cohomology. -/
noncomputable def pullback {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    DerivedQCoh X ⥤ DerivedQCoh Y :=
  (derivedQuasiCoherentModuleProperty Y).lift
    ((derivedQuasiCoherentModuleProperty X).ι ⋙ modulePullbackDerived f)
    (fun E ↦ pullback.mapsTo f E.obj E.property)

namespace pullback

/-- Forgetting the restricted derived pullback recovers ambient derived pullback. -/
noncomputable def inclusionIso {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    pullback f ⋙ inclusion Y ≅ inclusion X ⋙ modulePullbackDerived f :=
  (derivedQuasiCoherentModuleProperty Y).liftCompιIso
    ((derivedQuasiCoherentModuleProperty X).ι ⋙ modulePullbackDerived f)
    (fun E ↦ mapsTo f E.obj E.property)

/-- The underlying derived module of restricted pullback is ambient derived pullback. -/
@[simp]
theorem obj_obj {Y X : AlgebraicSpace S} (f : Y ⟶ X) (E : DerivedQCoh X) :
    ((pullback f).obj E).obj = (modulePullbackDerived f).obj E.obj :=
  sorry

end pullback

/-- Exact derived pullback along `schemeEtaleRingedHom U` sends étale quasi-coherent
complexes on `U.left` to quasi-coherent complexes on `ofOver U`. -/
theorem smallEtaleToOfOver_mapsTo (U : Over S) :
    Scheme.DerivedQCoh.smallEtaleProperty U.left ≤
      (derivedQuasiCoherentModuleProperty (ofOver U)).inverseImage
        (IsFlat.exactPullback (schemeEtaleRingedHom U)).mapDerivedCategory :=
  sorry

/-- Exact derived identification of `D_QCoh` on the small étale site of a scheme `U`
over `S` with `D_QCoh` of the associated algebraic space `ofOver U`. -/
noncomputable def smallEtaleToOfOver (U : Over S) :
    Scheme.DerivedQCoh.SmallEtale U.left ⥤ DerivedQCoh (ofOver U) :=
  FullSubcategory.restrict
    (IsFlat.exactPullback (schemeEtaleRingedHom U)).mapDerivedCategory
    (smallEtaleToOfOver_mapsTo U)

/-- Forgetting quasi-coherence after `smallEtaleToOfOver` recovers ambient exact derived
pullback along `schemeEtaleRingedHom`. -/
noncomputable def smallEtaleToOfOver.inclusionIso (U : Over S) :
    smallEtaleToOfOver U ⋙ inclusion (ofOver U) ≅
      SmallEtale.inclusion U.left ⋙
        (IsFlat.exactPullback (schemeEtaleRingedHom U)).mapDerivedCategory :=
  FullSubcategory.restrict.compιIso
    (IsFlat.exactPullback (schemeEtaleRingedHom U)).mapDerivedCategory
    (smallEtaleToOfOver_mapsTo U)

/-- The identification `D_QCoh(𝒪_{U.left}) ⥤ D_QCoh(𝒪_{ofOver U})` of Lemma 75.4.2,
obtained by `ε*` to the small étale site of `U.left` followed by exact pullback along
`schemeEtaleRingedHom U`. -/
noncomputable def ofOverEpsilonStar (U : Over S) :
    Scheme.DerivedQCoh U.left ⥤ DerivedQCoh (ofOver U) :=
  Scheme.DerivedQCoh.epsilonStar U.left ⋙ smallEtaleToOfOver U

namespace ofOverEpsilonStar

/-- Composite `ε*` lands in `D_QCoh` of the associated algebraic space. -/
theorem mapsTo (U : Over S) (E : Scheme.DerivedQCoh U.left) :
    derivedQuasiCoherentModuleProperty (ofOver U)
      ((inclusion (ofOver U)).obj ((ofOverEpsilonStar U).obj E)) :=
  sorry

/-- The underlying derived module of `ofOverEpsilonStar` is ambient exact derived
pullback along `schemeEtaleRingedHom` of the étale image of `ε* E`. -/
@[simp]
theorem obj_obj (U : Over S) (E : Scheme.DerivedQCoh U.left) :
    ((ofOverEpsilonStar U).obj E).obj =
      ((IsFlat.exactPullback (schemeEtaleRingedHom U)).mapDerivedCategory).obj
        ((SmallEtale.inclusion U.left).obj
          ((Scheme.DerivedQCoh.epsilonStar U.left).obj E)) :=
  sorry

end ofOverEpsilonStar

/-- The comparison `D_QCoh(𝒪_{U.left}) ⥤ D_QCoh(𝒪_{ofOver U})` is an equivalence. -/
instance ofOverEpsilonStar_isEquivalence (U : Over S) :
    (ofOverEpsilonStar U).IsEquivalence :=
  sorry

/-- Remark 75.6.3 (1): derived pullback along a morphism of representable algebraic
spaces over `S` commutes with the identifications `D_QCoh(𝒪_{X0}) ⥤ D_QCoh(𝒪_X)` and
`D_QCoh(𝒪_{Y0}) ⥤ D_QCoh(𝒪_Y)` of Lemma 75.4.2. -/
@[stacks 08GH]
theorem ofOver_pullback_comm {X0 Y0 : Over S} (f0 : X0 ⟶ Y0) :
    IsIsomorphic
      (Scheme.DerivedQCoh.pullback f0.left ⋙ ofOverEpsilonStar X0)
      (ofOverEpsilonStar Y0 ⋙ pullback (ofOverMap f0)) :=
  sorry

/-- Remark 75.6.3 (2): if `f0` is quasi-compact and quasi-separated, equivalently if
`ofOverMap f0` is quasi-compact and quasi-separated, derived pushforward commutes with
the same identifications of Lemma 75.4.2. -/
@[stacks 08GH]
theorem ofOver_pushforward_comm {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [QuasiCompact (ofOverMap f0)] [QuasiSeparated (ofOverMap f0)] :
    IsIsomorphic
      (Scheme.DerivedQCoh.pushforward f0.left ⋙ ofOverEpsilonStar Y0)
      (ofOverEpsilonStar X0 ⋙ pushforward (ofOverMap f0)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
