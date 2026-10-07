module

public import stacks_project.Chap66.Lemma_66_33_1_Affine
public import stacks_project.Chap98.Lemma_98_9_3_FormalObject
public import stacks_project.Chap98.«98_9_3_1_Approximation»
public import stacks_project.Chap99.Lemma_99_15_2

/-!
# Lemma 99.15.9

The stack Curves over `specZ` has every Artin formal object effective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Functor
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- An Artin formal object of Curves over `specZ`: a complete local
`specZ`-algebra together with a compatible system of families of curves over
the truncations `Spec(R ⧸ m^{n+1})`. -/
structure FormalObject where
  /-- Complete local `specZ`-algebra underlying the formal object. -/
  base : CompleteLocalSAlgebra specZ
  /-- Stage `n` is the source object over `Spec(R ⧸ m^{n+1})`. -/
  objects : ℕ → Obj specZ
  /-- Transition over `Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2})`. -/
  step : ∀ n, objects n ⟶ objects (n + 1)
  /-- Stage `n` lies over `Spec(R ⧸ m^{n+1}) ⟶ specZ`. -/
  over_obj : ∀ n, (p specZ).obj (objects n) = base.stageOver n
  /-- The successor morphism lies over the truncation thickening in `Over specZ`. -/
  over_step : ∀ n, (p specZ).IsHomLift (base.stageHom n) (step n)

namespace FormalObject

/-- Package a complete local `specZ`-algebra and a compatible forward system as
a formal object of Curves. -/
def of (base : CompleteLocalSAlgebra specZ) (objects : ℕ → Obj specZ)
    (step : ∀ n, objects n ⟶ objects (n + 1))
    (over_obj : ∀ n, (p specZ).obj (objects n) = base.stageOver n)
    (over_step : ∀ n, (p specZ).IsHomLift (base.stageHom n) (step n)) :
    FormalObject where
  base := base
  objects := objects
  step := step
  over_obj := over_obj
  over_step := over_step

/-- The packaged formal object recovers the supplied complete local
`specZ`-algebra. -/
theorem of_base (base : CompleteLocalSAlgebra specZ) (objects : ℕ → Obj specZ)
    (step : ∀ n, objects n ⟶ objects (n + 1))
    (over_obj : ∀ n, (p specZ).obj (objects n) = base.stageOver n)
    (over_step : ∀ n, (p specZ).IsHomLift (base.stageHom n) (step n)) :
    (of base objects step over_obj over_step).base = base := sorry

/-- Stagewise specification of a formal object over the truncations of its
base. -/
theorem spec (ξ : FormalObject) (n : ℕ) :
    (p specZ).obj (ξ.objects n) = ξ.base.stageOver n ∧
      (p specZ).IsHomLift (ξ.base.stageHom n) (ξ.step n) := sorry

/-- The stagewise over-object and over-step conditions are equivalent to the
bundled pair of universal conditions. -/
theorem spec_iff (ξ : FormalObject) :
    (∀ n, (p specZ).obj (ξ.objects n) = ξ.base.stageOver n ∧
        (p specZ).IsHomLift (ξ.base.stageHom n) (ξ.step n)) ↔
      ((∀ n, (p specZ).obj (ξ.objects n) = ξ.base.stageOver n) ∧
        ∀ n, (p specZ).IsHomLift (ξ.base.stageHom n) (ξ.step n)) := sorry

/-- Unique factorization of a lift through a strongly cartesian arrow. -/
def factorCartesian {U V W : Over specZ} {x y z : Obj specZ} (f : V ⟶ U)
    (φ : y ⟶ x) (hφ : (p specZ).IsStronglyCartesian f φ) {g : W ⟶ V}
    {f' : W ⟶ U} (hf' : f' = g ≫ f) (φ' : z ⟶ x)
    (hφ' : (p specZ).IsHomLift f' φ') : z ⟶ y :=
  @IsStronglyCartesian.map _ _ _ _ (p specZ) _ _ _ _ f φ hφ _ _ g f' hf' φ' hφ'

/-- The comparison `factorCartesian` lies over the first factor of the base. -/
instance factorCartesian_isHomLift {U V W : Over specZ} {x y z : Obj specZ}
    (f : V ⟶ U) (φ : y ⟶ x) (hφ : (p specZ).IsStronglyCartesian f φ)
    {g : W ⟶ V} {f' : W ⟶ U} (hf' : f' = g ≫ f) (φ' : z ⟶ x)
    (hφ' : (p specZ).IsHomLift f' φ') :
    (p specZ).IsHomLift g (factorCartesian f φ hφ hf' φ' hφ') :=
  @IsStronglyCartesian.map_isHomLift _ _ _ _ (p specZ) _ _ _ _ f φ hφ _ _ g f'
    hf' φ' hφ'

/-- Restriction of a family of curves along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restrictionObj {R : CompleteLocalSAlgebra specZ} (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) : Obj specZ :=
  IsPreFibered.pullbackObj hx (R.truncationOverHom n)

/-- Cartesian lift of restriction along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restrictionHom {R : CompleteLocalSAlgebra specZ} (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    restrictionObj x hx n ⟶ x :=
  IsPreFibered.pullbackMap hx (R.truncationOverHom n)

/-- Restriction of `x` to stage `n` is cartesian over `truncationOverHom`. -/
instance restrictionHom_isCartesian {R : CompleteLocalSAlgebra specZ}
    (x : Obj specZ) (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    (p specZ).IsCartesian (R.truncationOverHom n) (restrictionHom x hx n) :=
  IsPreFibered.pullbackMap.IsCartesian hx (R.truncationOverHom n)

/-- Restriction of `x` to stage `n` is strongly cartesian. -/
instance restrictionHom_isStronglyCartesian {R : CompleteLocalSAlgebra specZ}
    (x : Obj specZ) (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    (p specZ).IsStronglyCartesian (R.truncationOverHom n)
      (restrictionHom x hx n) :=
  IsFibered.isStronglyCartesian_of_isCartesian (p specZ)
    (R.truncationOverHom n) (restrictionHom x hx n)

/-- Stage `n` of the restricted system lies over `Spec(R ⧸ m^{n+1})`. -/
theorem restrictionObj_over {R : CompleteLocalSAlgebra specZ} (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    (p specZ).obj (restrictionObj x hx n) = R.stageOver n := sorry

/-- Successor map of restrictions, obtained from transitivity of pullback along
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R ⧸ m^{n+2}) ⟶ Spec(R)`. -/
def restrictionStep {R : CompleteLocalSAlgebra specZ} (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    restrictionObj x hx n ⟶ restrictionObj x hx (n + 1) :=
  factorCartesian (R.truncationOverHom (n + 1)) (restrictionHom x hx (n + 1))
    (restrictionHom_isStronglyCartesian x hx (n + 1))
    (R.truncationOverHom_comp n) (restrictionHom x hx n)
    (restrictionHom_isCartesian x hx n).toIsHomLift

/-- Successor maps of restrictions lift the truncated thickenings. -/
instance restrictionStep_isHomLift {R : CompleteLocalSAlgebra specZ}
    (x : Obj specZ) (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    (p specZ).IsHomLift (R.stageHom n) (restrictionStep x hx n) :=
  factorCartesian_isHomLift (R.truncationOverHom (n + 1))
    (restrictionHom x hx (n + 1)) (restrictionHom_isStronglyCartesian x hx (n + 1))
    (R.truncationOverHom_comp n) (restrictionHom x hx n)
    (restrictionHom_isCartesian x hx n).toIsHomLift

/-- The successor comparison factors the cartesian restriction of stage `n`. -/
theorem restrictionHom_fac {R : CompleteLocalSAlgebra specZ} (x : Obj specZ)
    (hx : (p specZ).obj x = Over.mk R.toS) (n : ℕ) :
    restrictionStep x hx n ≫ restrictionHom x hx (n + 1) =
      restrictionHom x hx n := sorry

/-- A formal object of Curves over `specZ` is effective if it arises by
restriction from some family of curves over `Spec(R)`, with the restrictions
forming a transition-compatible system of fibre isomorphisms. -/
class IsEffective (ξ : FormalObject) : Prop where
  /-- There is a family of curves over `Spec(R)` together with fibre
  isomorphisms from its restrictions that intertwine the successor maps. -/
  exists_algebraization :
    ∃ (x : Obj specZ) (hx : (p specZ).obj x = Over.mk ξ.base.toS)
      (α : ∀ n, restrictionObj x hx n ≅ ξ.objects n),
      (∀ n, (p specZ).IsHomLift (𝟙 (ξ.base.stageOver n)) (α n).hom) ∧
        ∀ n, restrictionStep x hx n ≫ (α (n + 1)).hom =
          (α n).hom ≫ ξ.step n

/-- Effectiveness is existence of an algebraization whose restrictions recover
the stages by a transition-compatible system of fibre isomorphisms. -/
theorem isEffective_iff (ξ : FormalObject) :
    IsEffective ξ ↔
      ∃ (x : Obj specZ) (hx : (p specZ).obj x = Over.mk ξ.base.toS)
        (α : ∀ n, restrictionObj x hx n ≅ ξ.objects n),
        (∀ n, (p specZ).IsHomLift (𝟙 (ξ.base.stageOver n)) (α n).hom) ∧
          ∀ n, restrictionStep x hx n ≫ (α (n + 1)).hom =
            (α n).hom ≫ ξ.step n := sorry

end FormalObject

/-- Lemma 99.15.9: the stack Curves over the base scheme `specZ` has every
Artin formal object effective. Equivalently, every `ξ : FormalObject`
satisfies `FormalObject.IsEffective`. -/
@[stacks 0D58]
instance instFormalObjectIsEffective (ξ : FormalObject) :
    FormalObject.IsEffective ξ := sorry

/-- Every formal object of Curves over `specZ` arises by restriction from some
family of curves over `Spec(R)`, compatibly with the transition maps. -/
theorem exists_algebraization (ξ : FormalObject) :
    ∃ (x : Obj specZ) (hx : (p specZ).obj x = Over.mk ξ.base.toS)
      (α : ∀ n, FormalObject.restrictionObj x hx n ≅ ξ.objects n),
      (∀ n, (p specZ).IsHomLift (𝟙 (ξ.base.stageOver n)) (α n).hom) ∧
        ∀ n, FormalObject.restrictionStep x hx n ≫ (α (n + 1)).hom =
          (α n).hom ≫ ξ.step n := sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
