module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap85.Lemma_85_34_2_Pullback
public import stacks_project.Chap85.Lemma_85_34_5_Comparison

/-!
# Stage module pullbacks and spaces-étale module cohomology

Pullback of an `𝒪_X`-module to a simplicial stage `U_n,étale`, and the
cohomology groups `H^q_étale(Y, F)` obtained from unbounded derived global
sections after the carrier lift to universe `u + 1`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open Functor RingedSite.Hom RingedSite.ToposHom
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}}

/-- Restriction of scalars along the inverse-image structure map of
`spacesRingedToposHom f` is a right adjoint, so module pullback exists. -/
instance restrictScalars_spacesRingedToposHom_isRightAdjoint
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (SheafOfModules.restrictScalars.{u}
      (spacesRingedToposHom f).structureMap).IsRightAdjoint :=
  sorry

/-- Module pushforward along `spacesRingedHom f` is a right adjoint. -/
instance modulePushforward_spacesRingedHom_isRightAdjoint
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((spacesRingedHom f).modulePushforward.{u}).IsRightAdjoint :=
  sorry

variable {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Inverse image of an `𝒪_X`-module along the degree-`n` map of an augmentation
`a : U ⟶ X`, landing on `U_n,étale`. This is the sheaf `F_n` of the
fppf-hypercovering spectral sequence for quasi-coherent modules. -/
def stageModulePullback (n : ℕ) :
    RingedSite.ModuleCat.{u} (spacesRingedSite X) ⥤
      RingedSite.ModuleCat.{u} (spacesRingedSite (U.obj (op ⦋n⦌))) :=
  (spacesRingedToposHom (a.app (op ⦋n⦌))).modulePullback

/-- `stageModulePullback a n` is module pullback along `spacesRingedToposHom` of
the degree-`n` augmentation map. -/
theorem stageModulePullback_eq (n : ℕ) :
    stageModulePullback a n =
      (spacesRingedToposHom (a.app (op ⦋n⦌))).modulePullback :=
  sorry

/-- Evaluating `stageModulePullback a n` on `F` is module pullback of `F` along the
degree-`n` augmentation map. -/
theorem stageModulePullback_obj (n : ℕ)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) :
    (stageModulePullback a n).obj F =
      (spacesRingedToposHom (a.app (op ⦋n⦌))).modulePullback.obj F :=
  sorry

/-- Stage pullback `F_n` is isomorphic to Hom-level module pullback along
`spacesRingedHom` of the degree-`n` augmentation map. -/
theorem stageModulePullback_hom (n : ℕ)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) :
    Nonempty
      ((stageModulePullback a n).obj F ≅
        ((spacesRingedHom (a.app (op ⦋n⦌))).modulePullback.{u}).obj F) :=
  sorry

/-- Stage pullback of a quasi-coherent `𝒪_X`-module remains quasi-coherent on
`U_n,étale`. -/
theorem stageModulePullback_mem_spacesQuasiCoherentModuleProperty (n : ℕ)
    {F : RingedSite.ModuleCat.{u} (spacesRingedSite X)}
    (hF : spacesQuasiCoherentModuleProperty X F) :
    spacesQuasiCoherentModuleProperty (U.obj (op ⦋n⦌))
      ((stageModulePullback a n).obj F) :=
  sorry

/-- The module `F` placed in `D(𝒪_Y)` in degree `0` after the carrier lift to
universe `u + 1`. -/
def spacesEtaleModuleSingle (Y : AlgebraicSpace S)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite Y)) :
    ModuleDerived.{u + 1} (spacesRingedSite Y) :=
  (moduleLocalization.{u + 1} (spacesRingedSite Y)).obj
    ((HomotopyCategory.singleFunctor
        (RingedSite.ModuleCat.{u + 1} (spacesRingedSite Y)) 0).obj
      (RingedSite.Module.carrierLift (spacesRingedSite Y) F))

/-- `spacesEtaleModuleSingle Y F` is the localization of the degree-zero complex on
the carrier lift of `F`. -/
theorem spacesEtaleModuleSingle_eq (Y : AlgebraicSpace S)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite Y)) :
    spacesEtaleModuleSingle Y F =
      (moduleLocalization.{u + 1} (spacesRingedSite Y)).obj
        ((HomotopyCategory.singleFunctor
            (RingedSite.ModuleCat.{u + 1} (spacesRingedSite Y)) 0).obj
          (RingedSite.Module.carrierLift (spacesRingedSite Y) F)) :=
  sorry

/-- Spaces-étale cohomology `H^q_étale(Y, F)` of an `𝒪_Y`-module, as homology of
`RΓ(Y_étale, F[0])` after the carrier lift. -/
abbrev spacesEtaleModuleCohomology (Y : AlgebraicSpace S)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite Y)) (q : ℕ) :
    AddCommGrpCat.{u + 1} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
    ((moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite Y)).obj
      (spacesEtaleModuleSingle Y F))

/-- `spacesEtaleModuleCohomology Y F q` is homology of derived global sections of
the degree-zero carrier lift of `F`. -/
theorem spacesEtaleModuleCohomology_eq (Y : AlgebraicSpace S)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite Y)) (q : ℕ) :
    spacesEtaleModuleCohomology Y F q =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
        ((moduleGlobalSectionsDerived.{u + 1} (spacesRingedSite Y)).obj
          (spacesEtaleModuleSingle Y F)) :=
  sorry

/-- The first-page target `H^q_étale(U_p, F_p)` of the fppf-hypercovering spectral
sequence for an `𝒪_X`-module. -/
abbrev stageModuleCohomology (F : RingedSite.ModuleCat.{u} (spacesRingedSite X))
    (p q : ℕ) : AddCommGrpCat.{u + 1} :=
  spacesEtaleModuleCohomology (U.obj (op ⦋p⦌)) ((stageModulePullback a p).obj F) q

/-- `stageModuleCohomology a F p q` is spaces-étale cohomology of the degree-`p`
stage pullback. -/
theorem stageModuleCohomology_eq (F : RingedSite.ModuleCat.{u} (spacesRingedSite X))
    (p q : ℕ) :
    stageModuleCohomology a F p q =
      spacesEtaleModuleCohomology (U.obj (op ⦋p⦌))
        ((stageModulePullback a p).obj F) q :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
