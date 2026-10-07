module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.RingTheory.Ideal.Maps
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Annihilator
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap67.Lemma_67_15_3_SchemeTheoreticSupport
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

/-!
# Scheme-theoretic support of a finite-type quasi-coherent module

The scheme-theoretic support of a finite-type quasi-coherent `𝒪_X`-module on an
algebraic space is the closed subspace cut out by the annihilator ideal of the
module on the small étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The scalar-action map from the universe-lifted structure module to the
internal endomorphism sheaf of `F`. -/
def annihilatorAction {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    unitModule (smallEtaleTopology X) (commStructureSheafLift X) ⟶
      (ihom (liftModule F)).obj (liftModule F) :=
  Annihilator.action (liftModule F)

/-- The scalar-action map is the ringed-site annihilator action of the
universe lift of `F`. -/
theorem annihilatorAction_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) :
    annihilatorAction F = Annihilator.action (liftModule F) :=
  sorry

/-- The annihilator of `F` as a subobject of the universe-lifted structure
module. -/
def annihilatorLiftSubobject {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) :
    Subobject (unitModule (smallEtaleTopology X) (commStructureSheafLift X)) :=
  kernelSubobject (annihilatorAction F)

/-- The lifted annihilator is the kernel subobject of the scalar-action map. -/
theorem annihilatorLiftSubobject_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) :
    annihilatorLiftSubobject F = kernelSubobject (annihilatorAction F) :=
  sorry

/-- The section ideal of the annihilator over an étale object, recast from the
universe-lifted commutative presentation. -/
def annihilatorSectionIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    Ideal ((structureSheaf X).obj.obj U) :=
  Ideal.comap (ULift.ringEquiv.{u, u + 1}.symm.toRingHom)
    (IdealSheaf.sections (annihilatorLiftSubobject F) U)

/-- The section ideal is the comap of the lifted annihilator section ideal along
the universe-lift ring equivalence. -/
theorem annihilatorSectionIdeal_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    annihilatorSectionIdeal F U =
      Ideal.comap (ULift.ringEquiv.{u, u + 1}.symm.toRingHom)
        (IdealSheaf.sections (annihilatorLiftSubobject F) U) :=
  sorry

/-- Restriction of annihilator sections remains in the annihilator. -/
theorem map_mem_annihilatorSectionIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) {U V : (smallEtaleSite X)ᵒᵖ} (f : U ⟶ V)
    (a : annihilatorSectionIdeal F U) :
    (structureSheaf X).obj.map f (a : (structureSheaf X).obj.obj U) ∈
      annihilatorSectionIdeal F V :=
  sorry

/-- The annihilator of `F` as an `𝒪_X`-module, with sections the annihilator
ideals of the universe-lifted presentation. -/
def annihilatorSheaf {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    X.Modules where
  val :=
    { obj := fun U => ModuleCat.of _ (annihilatorSectionIdeal F U)
      map := fun {U V} f =>
        ModuleCat.ofHom
          (Y :=
            (ModuleCat.restrictScalars ((structureSheaf X).obj.map f).hom).obj
              (ModuleCat.of _ (annihilatorSectionIdeal F V)))
          { toFun := fun a =>
              ⟨(structureSheaf X).obj.map f (a : (structureSheaf X).obj.obj U),
                map_mem_annihilatorSectionIdeal F f a⟩
            map_add' := sorry
            map_smul' := sorry }
      map_id := sorry
      map_comp := sorry }
  isSheaf := sorry

/-- The canonical inclusion of the annihilator sheaf into `𝒪_X`. -/
def annihilatorι {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    annihilatorSheaf F ⟶ SheafOfModules.unit (structureSheaf X) where
  val :=
    { app := fun U =>
        ModuleCat.ofHom
          (Submodule.subtype (annihilatorSectionIdeal F U : Submodule _ _))
      naturality := sorry }

/-- The annihilator inclusion is a monomorphism. -/
instance annihilatorι_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) : Mono (annihilatorι F) :=
  sorry

/-- The annihilator inclusion is the recast of the ringed-site annihilator
inclusion of the universe lift of `F`. -/
theorem annihilatorι_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    ((annihilatorι F).val.app U).hom =
      Submodule.subtype (annihilatorSectionIdeal F U : Submodule _ _) :=
  sorry

/-- The annihilator ideal of an `𝒪_X`-module, as the kernel of the scalar-action
map recast to `X.Modules`. -/
def annihilatorIdeal {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    IdealSubobject X :=
  Subobject.mk (annihilatorι F)

/-- The annihilator ideal is the subobject represented by the annihilator
inclusion. -/
theorem annihilatorIdeal_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) :
    annihilatorIdeal F = Subobject.mk (annihilatorι F) :=
  sorry

/-- The annihilator of a finite-type quasi-coherent `𝒪_X`-module is
quasi-coherent. -/
instance instIsQuasiCoherent_annihilatorIdeal {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    IsQuasiCoherent (annihilatorIdeal F) :=
  sorry

/-- The scheme-theoretic support of a finite-type quasi-coherent `𝒪_X`-module is
the closed subspace of `X` cut out by the annihilator ideal. -/
def schemeTheoreticSupport {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] : ClosedSubspace X :=
  ClosedSubspace.ofQuasiCoherentIdeal (annihilatorIdeal F)

/-- The inclusion of the scheme-theoretic support is the closed-subspace
inclusion cut out by the annihilator ideal. -/
theorem schemeTheoreticSupport_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (schemeTheoreticSupport F).ι = subschemeι (annihilatorIdeal F) :=
  sorry

/-- The inclusion of the scheme-theoretic support of `F` is a scheme-theoretic
support in the sense of Lemma 67.15.3. -/
instance instIsSchemeTheoreticSupport_schemeTheoreticSupport {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    IsSchemeTheoreticSupport F (schemeTheoreticSupport F).ι :=
  sorry

/-- The scheme-theoretic support of `F` is the closed subspace cut out by
`annihilatorIdeal F`, and its inclusion is a least closed immersion through
which `F` is a quasi-coherent pushforward. -/
theorem schemeTheoreticSupport_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    IsSchemeTheoreticSupport F (schemeTheoreticSupport F).ι ∧
      (schemeTheoreticSupport F).ι = subschemeι (annihilatorIdeal F) ∧
        annihilatorIdeal F = Subobject.mk (annihilatorι F) :=
  sorry

/-- Any scheme-theoretic support of `F` is uniquely isomorphic over `X` to the
chosen scheme-theoretic support. -/
theorem existsUnique_iso_schemeTheoreticSupport {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsSchemeTheoreticSupport F i] :
    ∃! e : Z ≅ (schemeTheoreticSupport F).X,
      e.hom ≫ (schemeTheoreticSupport F).ι = i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
