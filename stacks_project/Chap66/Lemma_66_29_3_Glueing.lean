/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap66.Lemma_66_29_2_Pullback

/-!
# Glueing quasi-coherent modules on small étale sites of algebraic spaces

A quasi-coherent `𝒪_X`-module on `X_étale` determines a quasi-coherent `𝒪_U`-module
on `U_étale` for every object `U` of `X_étale`, together with module-pullback
transition isomorphisms along morphisms of `X_étale`. This module packages those
compatible quasi-coherent systems as a full subcategory of module glueing data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtaleQCohGlueing

variable {S : Scheme.{u}}

/-- Componentwise quasi-coherence of a compatible system of modules on the small étale
sites of schemes étale over an algebraic space. -/
abbrev isQuasicoherent (X : AlgebraicSpace S) :
    ObjectProperty (SmallEtaleModuleGlueing.category X) :=
  fun G ↦ ∀ U : smallEtaleSite X, (G.obj U).IsQuasicoherent

/-- Componentwise quasi-coherence implies each `F_U` is a quasi-coherent `𝒪_U`-module. -/
theorem isQuasicoherent_spec (X : AlgebraicSpace S)
    (G : SmallEtaleModuleGlueing.category X) :
    isQuasicoherent X G → ∀ U : smallEtaleSite X, (G.obj U).IsQuasicoherent :=
  sorry

/-- A compatible module system is quasi-coherent iff each component `F_U` is
quasi-coherent. -/
theorem isQuasicoherent_iff (X : AlgebraicSpace S)
    (G : SmallEtaleModuleGlueing.category X) :
    isQuasicoherent X G ↔ ∀ U : smallEtaleSite X, (G.obj U).IsQuasicoherent :=
  sorry

/-- The category of compatible systems of quasi-coherent modules on the small étale
sites of schemes étale over an algebraic space. -/
abbrev category (X : AlgebraicSpace S) :=
  (isQuasicoherent X).FullSubcategory

/-- The inclusion of compatible quasi-coherent systems into all compatible module
systems. -/
abbrev inclusion (X : AlgebraicSpace S) :
    category X ⥤ SmallEtaleModuleGlueing.category X :=
  (isQuasicoherent X).ι

/-- Module pullback of a quasi-coherent sheaf on `X_étale` yields a componentwise
quasi-coherent compatible system. -/
theorem fromModules_mapsTo (X : AlgebraicSpace S) :
    quasiCoherentModuleProperty X ≤
      (isQuasicoherent X).inverseImage (SmallEtaleModuleGlueing.fromModules X) :=
  sorry

/-- Reconstruction of a sheaf of modules from a componentwise quasi-coherent system
is quasi-coherent. -/
theorem toModules_mapsTo (X : AlgebraicSpace S) :
    isQuasicoherent X ≤
      (quasiCoherentModuleProperty X).inverseImage (SmallEtaleModuleGlueing.toModules X) :=
  sorry

/-- The compatible quasi-coherent system associated to a quasi-coherent module on
`X_étale`. -/
def ofQCoh {X : AlgebraicSpace S} (F : QCoh X) : category X where
  obj := (SmallEtaleModuleGlueing.fromModules X).obj F.obj
  property := fromModules_mapsTo X F.obj F.property

/-- The underlying compatible module system of `ofQCoh F` is module pullback of the
underlying module of `F`. -/
theorem ofQCoh_obj {X : AlgebraicSpace S} (F : QCoh X) :
    (ofQCoh F).obj = (SmallEtaleModuleGlueing.fromModules X).obj F.obj :=
  rfl

/-- Quasi-coherent modules on `X_étale`, viewed as compatible systems of quasi-coherent
modules on all `U_étale`. -/
def fromQCoh (X : AlgebraicSpace S) : QCoh X ⥤ category X :=
  FullSubcategory.restrict (SmallEtaleModuleGlueing.fromModules X) (fromModules_mapsTo X)

/-- The component of `fromQCoh` at `U` is module pullback along the structure morphism. -/
theorem fromQCoh_obj {X : AlgebraicSpace S} (F : QCoh X) (U : smallEtaleSite X) :
    ((fromQCoh X).obj F).obj.obj U = (Modules.pullback U.hom).obj F.obj :=
  sorry

/-- The component of `fromQCoh` at `U` is the underlying module of quasi-coherent
pullback along the structure morphism. -/
theorem fromQCoh_obj_qcoh {X : AlgebraicSpace S} (F : QCoh X) (U : smallEtaleSite X) :
    ((fromQCoh X).obj F).obj.obj U = ((QCoh.pullback U.hom).obj F).obj :=
  sorry

/-- Transitions of `fromQCoh.obj F` are the module-pullback comparisons of the
underlying module. -/
theorem fromQCoh_transition {X : AlgebraicSpace S} (F : QCoh X)
    {U V : smallEtaleSite X} (f : V ⟶ U) :
    ((fromQCoh X).obj F).obj.transition f =
      SmallEtaleModuleGlueing.fromModulesTransition F.obj f :=
  sorry

/-- Reconstruction of a quasi-coherent sheaf on `X_étale` from a compatible
quasi-coherent system. -/
def toQCoh (X : AlgebraicSpace S) : category X ⥤ QCoh X :=
  FullSubcategory.restrict (SmallEtaleModuleGlueing.toModules X) (toModules_mapsTo X)

/-- The underlying module of `toQCoh.obj G` is the reconstructed module of the
forgotten compatible system. -/
theorem toQCoh_obj {X : AlgebraicSpace S} (G : category X) :
    ((toQCoh X).obj G).obj = (SmallEtaleModuleGlueing.toModules X).obj G.obj :=
  sorry

/-- Quasi-coherent modules on `X_étale` are equivalent to compatible systems of
quasi-coherent modules on all `U_étale`. -/
instance fromQCoh_isEquivalence (X : AlgebraicSpace S) :
    (fromQCoh X).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtaleQCohGlueing
