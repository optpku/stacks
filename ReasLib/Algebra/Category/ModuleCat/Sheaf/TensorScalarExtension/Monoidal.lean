module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TensorScalarExtension
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SameSiteTensorExtension.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor

/-!
# Tensor comparison for tensor-and-sheafification scalar extension

The sectionwise base-change maps descend through the existing module
sheafification. The lifting comparison uses the two actual adjunctions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe c v w

namespace SheafOfModules.TensorScalarExtension.Commutative

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {R R' : Sheaf J CommRingCat.{w}} (α : R ⟶ R')

abbrev sourceRing := Sheaf.ringSheafOfComm R
abbrev targetRing := Sheaf.ringSheafOfComm R'

/-- The original ring map in the canonical underlying ring presentation. -/
abbrev scalarMap : sourceRing (R := R) ⟶ targetRing (R' := R') :=
  Sheaf.ringSheafOfCommMap α

/-- Commutativity in the underlying ring-sheaf presentation uses the original operations. -/
theorem source_mul_comm (U : Cᵒᵖ) (x y : (sourceRing (R := R)).obj.obj U) :
    x * y = y * x := by
  exact @mul_comm (R.obj.obj U) inferInstance x y

/-- The target underlying ring sheaf retains commutativity. -/
theorem target_mul_comm (U : Cᵒᵖ) (x y : (targetRing (R' := R')).obj.obj U) :
    x * y = y * x := by
  exact @mul_comm (R'.obj.obj U) inferInstance x y

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The specified tensor-and-sheafification functor on commutative coefficients. -/
abbrev scalarExtension := functor (scalarMap α)
  (source_mul_comm (R := R)) (target_mul_comm (R' := R'))

local instance sourceMonoidal :
    MonoidalCategory (SheafOfModules.{w} (sourceRing (R := R))) :=
  SheafOfModules.RingedSite.moduleMonoidalCategory R

local instance targetMonoidal :
    MonoidalCategory (SheafOfModules.{w} (targetRing (R' := R'))) :=
  SheafOfModules.RingedSite.moduleMonoidalCategory R'

local instance sourcePresheafMonoidal :
    MonoidalCategory (PresheafOfModules.{w} (sourceRing (R := R)).obj) :=
  PresheafOfModules.monoidalCategory (R := R.obj)

local instance targetPresheafMonoidal :
    MonoidalCategory (PresheafOfModules.{w} (targetRing (R' := R')).obj) :=
  PresheafOfModules.monoidalCategory (R := R'.obj)

/-- Both composites are the specified left adjoints of the same
forget-and-restrict functor. -/
def sheafificationCompIso :
    PresheafOfModules.sheafification (R₀ := (sourceRing (R := R)).obj)
        (𝟙 (sourceRing (R := R)).obj) ⋙ scalarExtension α ≅
      PresheafOfModules.SameSiteTensorExtension.functor α.hom ⋙
        PresheafOfModules.sheafification (R₀ := (targetRing (R' := R')).obj)
          (𝟙 (targetRing (R' := R')).obj) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (sourceRing (R := R)).obj)).comp
      (adjunction (scalarMap α) (source_mul_comm (R := R)) (target_mul_comm (R' := R')))).leftAdjointUniq
    ((PresheafOfModules.SameSiteTensorExtension.adjunction α.hom).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 (targetRing (R' := R')).obj)))

/-- The explicit presheaf tensor maps followed by actual sheafification. -/
@[implicit_reducible]
def compositeMonoidal :
    (PresheafOfModules.SameSiteTensorExtension.functor α.hom ⋙
      PresheafOfModules.sheafification (R₀ := (targetRing (R' := R')).obj)
        (𝟙 (targetRing (R' := R')).obj)).Monoidal :=
  @Functor.Monoidal.instComp _ _ _ _ _ _ _ _ _
    (PresheafOfModules.SameSiteTensorExtension.functor α.hom)
    (PresheafOfModules.sheafification (R₀ := (targetRing (R' := R')).obj)
      (𝟙 (targetRing (R' := R')).obj))
    (PresheafOfModules.SameSiteTensorExtension.coreMonoidal α.hom).toMonoidal
    (SheafOfModules.RingedSite.Tensor.sheafificationMonoidal R')

set_option backward.isDefEq.respectTransparency false in
/-- Descend the actual sectionwise strong-monoidal core to module sheaves. -/
def coreMonoidal : (scalarExtension α).CoreMonoidal := by
  let L := PresheafOfModules.sheafification (R₀ := (sourceRing (R := R)).obj)
    (𝟙 (sourceRing (R := R)).obj)
  let G := PresheafOfModules.SameSiteTensorExtension.functor α.hom ⋙
    PresheafOfModules.sheafification (R₀ := (targetRing (R' := R')).obj)
      (𝟙 (targetRing (R' := R')).obj)
  let W := SheafOfModules.RingedSite.Tensor.weakEquivalences R
  letI : L.Monoidal := SheafOfModules.RingedSite.Tensor.sheafificationMonoidal R
  letI : G.Monoidal := by
    change (PresheafOfModules.SameSiteTensorExtension.functor α.hom ⋙
      PresheafOfModules.sheafification (R₀ := (targetRing (R' := R')).obj)
        (𝟙 (targetRing (R' := R')).obj)).Monoidal
    exact compositeMonoidal α
  letI : Localization.Lifting L W G (scalarExtension α) := ⟨sheafificationCompIso α⟩
  exact Localization.Monoidal.functorCoreMonoidalOfComp L W (scalarExtension α) G

/-- The sheaf tensor comparison has both components supplied by descent of
actual sectionwise base-change maps. -/
def tensorIso (M N : SheafOfModules.{w} (sourceRing (R := R))) :
    (scalarExtension α).obj M ⊗ (scalarExtension α).obj N ≅
      (scalarExtension α).obj (M ⊗ N) :=
  (coreMonoidal α).μIso M N

/-- The unit comparison comes from the actual scalar-extension unit maps. -/
def unitIso : 𝟙_ (SheafOfModules.{w} (targetRing (R' := R'))) ≅
    (scalarExtension α).obj (𝟙_ (SheafOfModules.{w} (sourceRing (R := R)))) :=
  (coreMonoidal α).εIso

end SheafOfModules.TensorScalarExtension.Commutative
