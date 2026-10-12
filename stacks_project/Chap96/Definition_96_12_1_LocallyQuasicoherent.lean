/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Definition_96_4_3_Sheaf
public import stacks_project.Chap96.Definition_96_12_1_Restriction

/-!
# Locally quasi-coherent modules on a groupoid fibration

A presheaf of `𝒪_X`-modules on a category fibred in groupoids is locally
quasi-coherent when it is an étale sheaf and every restriction to a small
étale site `U_étale` is quasi-coherent. This is the Stacks nonstandard
notation `LQCoh`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.AssociatedModule

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Slice sites of the small étale topology support composition with the
ring-to-abelian-group forgetful functor. -/
instance smallEtaleOver_hasSheafCompose (U : Scheme.{u})
    (V : SmallStandardTopology.etale.site U) :
    ((SmallStandardTopology.etale.topology U).over V).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- A presheaf of `𝒪_X`-modules is locally quasi-coherent when it is a sheaf
for the étale topology and, for every object `x` of `X` with `U = p(x)`, the
restriction `x* F|_{U_étale}` is a quasi-coherent sheaf on the small étale
site of `U`. -/
class IsLocallyQuasicoherent
    (F : PresheafOfModules.{u} (structureSheaf X).obj) : Prop where
  /-- `F` is a sheaf for the associated étale topology of `X`. -/
  isEtaleSheaf : Presheaf.IsSheaf X.etaleTopology F.presheaf
  /-- Every small-étale restriction `x* F|_{U_étale}` is quasi-coherent. -/
  restrict_isQuasicoherent (x : X.total) :
    (restrictToSmallEtale F x isEtaleSheaf).IsQuasicoherent

/-- Locally quasi-coherent `𝒪_X`-modules, as an object property on presheaves
of modules. -/
abbrev isLocallyQuasicoherent (X : GroupoidsOver S) :
    ObjectProperty (PresheafOfModules.{u} (structureSheaf X).obj) :=
  IsLocallyQuasicoherent

/-- A presheaf of `𝒪_X`-modules is locally quasi-coherent if and only if it is
an étale sheaf and every small-étale restriction is quasi-coherent. -/
theorem isLocallyQuasicoherent_iff
    (F : PresheafOfModules.{u} (structureSheaf X).obj) :
    IsLocallyQuasicoherent F ↔
      ∃ hF : Presheaf.IsSheaf X.etaleTopology F.presheaf,
        ∀ x : X.total, (restrictToSmallEtale F x hF).IsQuasicoherent :=
  sorry

/-- Membership in `isLocallyQuasicoherent X` is the class
`IsLocallyQuasicoherent`. -/
theorem mem_isLocallyQuasicoherent
    (F : PresheafOfModules.{u} (structureSheaf X).obj) :
    isLocallyQuasicoherent X F ↔ IsLocallyQuasicoherent F :=
  sorry

/-- The unit presheaf of `𝒪_X`-modules is locally quasi-coherent. -/
instance instIsLocallyQuasicoherentUnit (X : GroupoidsOver S) :
    IsLocallyQuasicoherent (PresheafOfModules.unit (structureSheaf X).obj) :=
  sorry

/-- A locally quasi-coherent module is an étale sheaf. -/
theorem isEtaleSheaf_of_isLocallyQuasicoherent
    (F : PresheafOfModules.{u} (structureSheaf X).obj)
    [IsLocallyQuasicoherent F] :
    Presheaf.IsSheaf X.etaleTopology F.presheaf :=
  sorry

/-- Each small-étale restriction of a locally quasi-coherent module is
quasi-coherent. -/
instance instRestrictIsQuasicoherent
    (F : PresheafOfModules.{u} (structureSheaf X).obj)
    [h : IsLocallyQuasicoherent F] (x : X.total) :
    (restrictToSmallEtale F x h.isEtaleSheaf).IsQuasicoherent :=
  h.restrict_isQuasicoherent x

/-- Étale sheafness of an `𝒪_X`-module presheaf agrees with
`FiberedInGroupoids.IsSheafFor` at the étale topology. -/
theorem isEtaleSheaf_iff (F : PresheafOfModules.{u} (structureSheaf X).obj) :
    Presheaf.IsSheaf X.etaleTopology F.presheaf ↔
      FiberedInGroupoids.IsSheafFor X.p StandardTopology.etale F.presheaf :=
  sorry

end AlgebraicGeometry.GroupoidsOver
