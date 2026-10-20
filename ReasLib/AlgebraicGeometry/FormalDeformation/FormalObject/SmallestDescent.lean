module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SubringOver.Pushforward
public import ReasLib.AlgebraicGeometry.FormalDeformation.Along
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Nilpotency
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal

/-!
# Evaluation of morphisms of formal objects in `S_x`

A morphism of formal objects over a subring inclusion may be packaged at each
Artinian truncation as an object of `SubringOver`, then pushed along the
nilpotency-stage cofibered arrow of a test map out of the complete local base
to produce an object of `S_x`.
-/

@[expose] public section

open CategoryTheory
open Functor
open Functor.SubringOver
open ArtinianLocalAlgCat CompleteLocalAlgCat IsLocalRing

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject

noncomputable section

/-- Unique factorization of `α : R ⟶ inclusion.obj A` through the identity truncation
`R.truncation (nilpotencyIndex A)`. -/
def nilpotencyFactor {R : CompleteLocalAlgCat Λ k} {A : ArtinianLocalAlgCat Λ k}
    (α : R ⟶ inclusion.obj A) :
    R.truncation (nilpotencyIndex A) ⟶ A :=
  truncationHom α (nilpotencyIndex A) ≫ (truncationNilpotencyIso A).hom

/-- The cofibered pushforward of a formal object at the nilpotency stage of a test
map `α : ξ.base ⟶ inclusion.obj A`. -/
def testObj [IsFibered.InGroupoids p.op] (ξ : FormalObject p)
    {A : ArtinianLocalAlgCat Λ k} (α : ξ.base ⟶ inclusion.obj A) : F :=
  Along.pushforwardObj (ξ.over_obj (nilpotencyIndex A)) (nilpotencyFactor α)

/-- The cofibered arrow from the nilpotency stage of `ξ` to `testObj ξ α`. -/
def testPush [IsFibered.InGroupoids p.op] (ξ : FormalObject p)
    {A : ArtinianLocalAlgCat Λ k} (α : ξ.base ⟶ inclusion.obj A) :
    ξ.system.family (nilpotencyIndex A) ⟶ testObj ξ α :=
  Along.pushforwardMap (ξ.over_obj (nilpotencyIndex A)) (nilpotencyFactor α)

/-- `testObj ξ α` is the cofibered pushforward of the nilpotency stage of `ξ`
along `nilpotencyFactor α`. -/
theorem testObj_spec [IsFibered.InGroupoids p.op] (ξ : FormalObject p)
    {A : ArtinianLocalAlgCat Λ k} (α : ξ.base ⟶ inclusion.obj A) :
    testObj ξ α =
        Along.pushforwardObj (ξ.over_obj (nilpotencyIndex A)) (nilpotencyFactor α) ∧
      testPush ξ α =
        Along.pushforwardMap (ξ.over_obj (nilpotencyIndex A)) (nilpotencyFactor α) :=
  sorry

namespace Hom

variable {ξ' ξ : FormalObject p}

/-- A morphism of formal objects lies over a subring inclusion when its complete
local base map is injective and each truncated stage is injective on underlying
algebra maps. -/
def IsOverSubring (f : ξ' ⟶ ξ) : Prop :=
  Function.Injective f.base.hom ∧
    ∀ n : ℕ, Function.Injective (p.map (f.app n)).hom

/-- Lying over a subring inclusion is injectivity of the complete local base map
together with injectivity of every truncated stage. -/
theorem isOverSubring_iff (f : ξ' ⟶ ξ) :
    IsOverSubring f ↔
      Function.Injective f.base.hom ∧
        ∀ n : ℕ, Function.Injective (p.map (f.app n)).hom :=
  sorry

namespace IsOverSubring

/-- The complete local base map of a morphism over a subring inclusion is injective. -/
theorem injective_base {f : ξ' ⟶ ξ} (hf : IsOverSubring f) :
    Function.Injective f.base.hom :=
  sorry

/-- Each truncated stage of a morphism over a subring inclusion is injective. -/
theorem injective_app {f : ξ' ⟶ ξ} (hf : IsOverSubring f) (n : ℕ) :
    Function.Injective (p.map (f.app n)).hom :=
  sorry

end IsOverSubring

/-- Package the truncated stage `f.app n` as an object of `SubringOver` over
`ξ.system.family n`. -/
def stageSubringOver (f : ξ' ⟶ ξ) {n : ℕ}
    (happ : Function.Injective (p.map (f.app n)).hom) :
    SubringOver p (ξ.system.family n) :=
  SubringOver.mk (f.app n) happ

/-- The underlying arrow of `stageSubringOver f happ` is the truncated stage of `f`. -/
theorem stageSubringOver_arrow (f : ξ' ⟶ ξ) {n : ℕ}
    (happ : Function.Injective (p.map (f.app n)).hom) :
    arrow (stageSubringOver f happ) = f.app n :=
  sorry

/-- The packaged truncated stage lies over an injective algebra map. -/
theorem stageSubringOver_spec (f : ξ' ⟶ ξ) {n : ℕ}
    (happ : Function.Injective (p.map (f.app n)).hom) :
    Function.Injective (p.map (arrow (stageSubringOver f happ))).hom :=
  sorry

/-- The object of `S_x` obtained by pushing the nilpotency-stage of `f` along the
cofibered arrow `testPush ξ α` of a test map `α : ξ.base ⟶ inclusion.obj A`. -/
def subringOver [IsFibered.InGroupoids p.op] (f : ξ' ⟶ ξ)
    {A : ArtinianLocalAlgCat Λ k} (α : ξ.base ⟶ inclusion.obj A)
    (happ : Function.Injective (p.map (f.app (nilpotencyIndex A))).hom) :
    SubringOver p (testObj ξ α) :=
  (SubringOver.pushforward p (testPush ξ α)).obj (stageSubringOver f happ)

/-- The coimage pushforward of a truncated stage is an object of `S_x`. -/
theorem subringOver_spec [IsFibered.InGroupoids p.op] (f : ξ' ⟶ ξ)
    {A : ArtinianLocalAlgCat Λ k} (α : ξ.base ⟶ inclusion.obj A)
    (happ : Function.Injective (p.map (f.app (nilpotencyIndex A))).hom) :
    Function.Injective (p.map (arrow (subringOver f α happ))).hom :=
  sorry

/-- The domain of `subringOver f α happ` lies over the coimage of the composite of
the truncated stage with `testPush ξ α`. -/
theorem subringOver_obj_image [IsFibered.InGroupoids p.op] (f : ξ' ⟶ ξ)
    {A : ArtinianLocalAlgCat Λ k} (α : ξ.base ⟶ inclusion.obj A)
    (happ : Function.Injective (p.map (f.app (nilpotencyIndex A))).hom) :
    p.obj (subringOver f α happ).obj.left =
      image (p.map (arrow (stageSubringOver f happ) ≫ testPush ξ α)) :=
  sorry

/-- A morphism of formal objects is a smallest descent of a versal object when it
lies over a subring inclusion, every Artinian test map pushes the corresponding
square to a minimal object of `S_x`, and every incoming morphism of formal objects
is surjective on complete local bases. -/
def IsSmallestDescent [IsFibered.InGroupoids p.op] (f : ξ' ⟶ ξ) : Prop :=
  IsOverSubring f ∧
    (∀ (A : ArtinianLocalAlgCat Λ k) (α : ξ.base ⟶ inclusion.obj A)
        (happ : Function.Injective (p.map (f.app (nilpotencyIndex A))).hom),
      IsMinimal (subringOver f α happ)) ∧
    ∀ {ξ'' : FormalObject p} (g : ξ'' ⟶ ξ'), Function.Surjective g.base.hom

/-- Smallest descent is a subring-over morphism whose Artinian pushforwards are
minimal in `S_x` and whose incoming complete local base maps are surjective. -/
theorem isSmallestDescent_iff [IsFibered.InGroupoids p.op] (f : ξ' ⟶ ξ) :
    IsSmallestDescent f ↔
      IsOverSubring f ∧
        (∀ (A : ArtinianLocalAlgCat Λ k) (α : ξ.base ⟶ inclusion.obj A)
            (happ : Function.Injective (p.map (f.app (nilpotencyIndex A))).hom),
          IsMinimal (subringOver f α happ)) ∧
        ∀ {ξ'' : FormalObject p} (g : ξ'' ⟶ ξ'), Function.Surjective g.base.hom :=
  sorry

namespace IsSmallestDescent

/-- A smallest descent morphism lies over a subring inclusion. -/
theorem isOverSubring [IsFibered.InGroupoids p.op] {f : ξ' ⟶ ξ}
    (hf : IsSmallestDescent f) : IsOverSubring f :=
  sorry

/-- Artinian test maps push a smallest descent morphism to a minimal object of
`S_x`. -/
theorem pushforward_isMinimal [IsFibered.InGroupoids p.op] {f : ξ' ⟶ ξ}
    (hf : IsSmallestDescent f) {A : ArtinianLocalAlgCat Λ k}
    (α : ξ.base ⟶ inclusion.obj A)
    (happ : Function.Injective (p.map (f.app (nilpotencyIndex A))).hom) :
    IsMinimal (subringOver f α happ) :=
  sorry

/-- Morphisms of formal objects into the source of a smallest descent morphism are
surjective on complete local bases. -/
theorem surjective_incoming [IsFibered.InGroupoids p.op] {f : ξ' ⟶ ξ}
    (hf : IsSmallestDescent f) {ξ'' : FormalObject p} (g : ξ'' ⟶ ξ') :
    Function.Surjective g.base.hom :=
  sorry

end IsSmallestDescent

end Hom

end

end FormalObject

namespace FormalObject

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- A versal formal object of a category cofibered in groupoids satisfying (S1)
admits a morphism over a subring inclusion whose Artinian test pushforwards are
minimal and whose incoming formal-object morphisms are surjective on complete
local bases. -/
theorem exists_isSmallestDescent [IsFibered.InGroupoids p.op]
    [HasSchlessingerS1 p] (ξ : FormalObject p) [IsVersal ξ] :
    ∃ (ξ' : FormalObject p) (f : ξ' ⟶ ξ), Hom.IsSmallestDescent f :=
  sorry

end FormalObject
