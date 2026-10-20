module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Invariant

/-!
# Categorical quotients of pre-relations

A categorical quotient of a pre-relation is a universal morphism equalizing its two
projections, either in the ambient over-category or in a full subcategory.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace PreRelation

/-- The cofork of the two projections of a pre-relation, with coequalizer candidate `φ`. -/
def cofork {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (h : P.IsInvariantHom φ) : Cofork P.t P.s :=
  Cofork.ofπ φ h

/-- The coequalizer candidate of `P.cofork h` is `φ`. -/
theorem cofork_π {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (h : P.IsInvariantHom φ) :
    (P.cofork h).π = φ :=
  sorry

/-- A morphism `φ : U ⟶ X` is a categorical quotient of `P` when it is invariant and
every invariant morphism out of `U` factors uniquely through `φ`. -/
@[mk_iff]
class IsCategoricalQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) : Prop where
  /-- The morphism equalizes the two projections of the pre-relation. -/
  invariant : P.IsInvariantHom φ
  /-- Every invariant morphism out of `U` factors uniquely through `φ`. -/
  unique_desc {Y : Over B} (ψ : U ⟶ Y) (hψ : P.IsInvariantHom ψ) :
    ∃! χ : X ⟶ Y, φ ≫ χ = ψ

/-- A categorical quotient is invariant, and every invariant morphism out of `U` factors
uniquely through it. -/
theorem IsCategoricalQuotient.spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) [P.IsCategoricalQuotient φ] :
    P.IsInvariantHom φ ∧
      ∀ {Y : Over B} (ψ : U ⟶ Y), P.IsInvariantHom ψ → ∃! χ : X ⟶ Y, φ ≫ χ = ψ :=
  sorry

/-- Being a categorical quotient is equivalent to the cofork of `φ` being colimiting. -/
theorem isCategoricalQuotient_iff_isColimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) :
    P.IsCategoricalQuotient φ ↔
      ∃ h : P.IsInvariantHom φ, Nonempty (IsColimit (P.cofork h)) :=
  sorry

/-- A colimiting cofork of the two projections is a categorical quotient. -/
theorem IsCategoricalQuotient.of_isColimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (h : P.IsInvariantHom φ)
    (H : IsColimit (P.cofork h)) : P.IsCategoricalQuotient φ :=
  sorry

/-- A morphism `φ : U ⟶ X` is a categorical quotient of `P` in a full subcategory `C`
when the relevant objects lie in `C`, `φ` is invariant, and invariant morphisms in `C`
factor uniquely through `φ`. -/
@[mk_iff]
class IsCategoricalQuotientIn {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (C : ObjectProperty (Over B)) (φ : U ⟶ X) : Prop where
  /-- The space `U` lies in `C`. -/
  obj_U : C U
  /-- The source of the pre-relation lies in `C`. -/
  obj_R : C P.left
  /-- The target of `φ` lies in `C`. -/
  obj_X : C X
  /-- The morphism equalizes the two projections of the pre-relation. -/
  invariant : P.IsInvariantHom φ
  /-- Every invariant morphism in `C` out of `U` factors uniquely through `φ`. -/
  unique_desc {Y : Over B} (hY : C Y) (ψ : U ⟶ Y) (hψ : P.IsInvariantHom ψ) :
    ∃! χ : X ⟶ Y, φ ≫ χ = ψ

/-- A categorical quotient in `C` is membership of the relevant objects in `C`, together
with invariance and unique factorization among invariant morphisms in `C`. -/
theorem isCategoricalQuotientIn_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (C : ObjectProperty (Over B)) (φ : U ⟶ X) :
    P.IsCategoricalQuotientIn C φ ↔
      C U ∧ C P.left ∧ C X ∧ P.IsInvariantHom φ ∧
        ∀ {Y : Over B} (hY : C Y) (ψ : U ⟶ Y),
          P.IsInvariantHom ψ → ∃! χ : X ⟶ Y, φ ≫ χ = ψ :=
  sorry

/-- An object of `Over B` as an object of the full subcategory cut out by `C`. -/
def asObj {S : Scheme.{u}} {B : AlgebraicSpace S} {C : ObjectProperty (Over B)}
    {X : Over B} (hX : C X) : C.FullSubcategory :=
  ⟨X, hX⟩

/-- The underlying object of `asObj hX` is `X`. -/
theorem asObj_obj {S : Scheme.{u}} {B : AlgebraicSpace S} {C : ObjectProperty (Over B)}
    {X : Over B} (hX : C X) : (asObj hX).obj = X :=
  sorry

/-- In a full subcategory, the two projections of a pre-relation equalize an invariant
morphism. -/
theorem coforkIn_condition {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {C : ObjectProperty (Over B)} {φ : U ⟶ X}
    (hU : C U) (hR : C P.left) (hX : C X) (hφ : P.IsInvariantHom φ) :
    (ObjectProperty.homMk P.t : asObj hR ⟶ asObj hU) ≫
        (ObjectProperty.homMk φ : asObj hU ⟶ asObj hX) =
      (ObjectProperty.homMk P.s : asObj hR ⟶ asObj hU) ≫
        (ObjectProperty.homMk φ : asObj hU ⟶ asObj hX) :=
  sorry

/-- The cofork of a pre-relation in a full subcategory, with coequalizer candidate `φ`. -/
def coforkIn {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {C : ObjectProperty (Over B)} {φ : U ⟶ X}
    (hU : C U) (hR : C P.left) (hX : C X) (hφ : P.IsInvariantHom φ) :
    Cofork (ObjectProperty.homMk P.t : asObj hR ⟶ asObj hU)
      (ObjectProperty.homMk P.s : asObj hR ⟶ asObj hU) :=
  Cofork.ofπ (ObjectProperty.homMk φ : asObj hU ⟶ asObj hX)
    (P.coforkIn_condition hU hR hX hφ)

/-- The coequalizer candidate of `P.coforkIn hU hR hX hφ` is `φ` in the full subcategory. -/
theorem coforkIn_π {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {C : ObjectProperty (Over B)} {φ : U ⟶ X}
    (hU : C U) (hR : C P.left) (hX : C X) (hφ : P.IsInvariantHom φ) :
    (P.coforkIn hU hR hX hφ).π = ObjectProperty.homMk φ :=
  sorry

/-- Being a categorical quotient in `C` is equivalent to the cofork of `φ` in `C` being
colimiting. -/
theorem isCategoricalQuotientIn_iff_isColimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (C : ObjectProperty (Over B)) (φ : U ⟶ X) :
    P.IsCategoricalQuotientIn C φ ↔
      ∃ (hU : C U) (hR : C P.left) (hX : C X) (hφ : P.IsInvariantHom φ),
        Nonempty (IsColimit (P.coforkIn hU hR hX hφ)) :=
  sorry

/-- A colimiting cofork in `C` is a categorical quotient in `C`. -/
theorem IsCategoricalQuotientIn.of_isColimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (C : ObjectProperty (Over B)) {φ : U ⟶ X}
    (hU : C U) (hR : C P.left) (hX : C X) (hφ : P.IsInvariantHom φ)
    (H : IsColimit (P.coforkIn hU hR hX hφ)) : P.IsCategoricalQuotientIn C φ :=
  sorry

/-- An ambient categorical quotient whose objects lie in `C` is a categorical quotient
in `C`. -/
instance instIsCategoricalQuotientIn_of_isCategoricalQuotient {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U X : Over B} {P : PreRelation U}
    {C : ObjectProperty (Over B)} {φ : U ⟶ X} [h : P.IsCategoricalQuotient φ]
    [C.Is U] [C.Is P.left] [C.Is X] : P.IsCategoricalQuotientIn C φ where
  obj_U := C.prop_of_is U
  obj_R := C.prop_of_is P.left
  obj_X := C.prop_of_is X
  invariant := h.invariant
  unique_desc := sorry

/-- A categorical quotient in the full subcategory of all algebraic spaces over `B` is a
categorical quotient. -/
instance instIsCategoricalQuotient_of_top {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} {P : PreRelation U} {φ : U ⟶ X}
    [h : P.IsCategoricalQuotientIn (⊤ : ObjectProperty (Over B)) φ] :
    P.IsCategoricalQuotient φ where
  invariant := h.invariant
  unique_desc := sorry

/-- A categorical quotient is a categorical quotient in the full subcategory of all
algebraic spaces over `B`. -/
theorem isCategoricalQuotient_iff_in_top {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) :
    P.IsCategoricalQuotient φ ↔
      P.IsCategoricalQuotientIn (⊤ : ObjectProperty (Over B)) φ :=
  sorry

end PreRelation
end AlgebraicGeometry.AlgebraicSpace

/-- Two categorical quotients of a pre-relation are uniquely isomorphic. -/
theorem AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotient.existsUniqueIso
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X Y : Over B} (P : PreRelation U) {φ : U ⟶ X} {ψ : U ⟶ Y}
    (hφ : P.IsCategoricalQuotient φ) (hψ : P.IsCategoricalQuotient ψ) :
    ∃! e : X ≅ Y, φ ≫ e.hom = ψ := sorry

/-- Two categorical quotients in a full subcategory are uniquely isomorphic. -/
theorem AlgebraicGeometry.AlgebraicSpace.PreRelation.IsCategoricalQuotientIn.existsUniqueIso
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X Y : Over B} (P : PreRelation U) (C : ObjectProperty (Over B))
    {φ : U ⟶ X} {ψ : U ⟶ Y}
    (hφ : P.IsCategoricalQuotientIn C φ) (hψ : P.IsCategoricalQuotientIn C ψ) :
    ∃! e : X ≅ Y, φ ≫ e.hom = ψ := sorry
