/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded algebra sheaves

This leaf owns differential graded algebra objects in sheaves of modules over a commutative ring
sheaf on an arbitrary site.  It uses the canonical monoidal structure on module sheaves, while
keeping the cochain-complex differential and monoidal unit explicit rather than identifying a
differential graded algebra with an ordinary graded algebra sheaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

-- Local declaration justification (parser conflict): this lexical alias avoids introducing a
-- public `Mod(𝒪)` notation overlapping the established graded-module `Mod(...)` scopes; it
-- installs neither mathematical data nor typeclass instances.
local notation "ModO" => ringedSiteModuleCategory J 𝒪
-- Local declaration justification (parser conflict): this complex alias is tied to the preceding
-- ambient-module parser boundary and installs neither mathematical data nor a typeclass instance.
local notation "CpxO" => CochainComplex ModO ℤ

/-- Transport the left Leibniz term of a differential graded algebra sheaf to degree
`n + m + 1`. -/
theorem differentialGradedAlgebra_leftLeibniz_index (n m : ℤ) :
    (n + 1) + m = n + m + 1 := sorry

/-- Transport the right Leibniz term of a differential graded algebra sheaf to degree
`n + m + 1`. -/
theorem differentialGradedAlgebra_rightLeibniz_index (n m : ℤ) :
    n + (m + 1) = n + m + 1 := sorry

/-- Definition 24.12.1 (1): a sheaf of differential graded `𝒪`-algebras is a cochain complex of
`𝒪`-modules equipped with degreewise multiplication, a unit, and the graded Leibniz rule. -/
@[stacks 0FRF]
structure DifferentialGradedAlgebra where
  /-- The underlying cochain complex of `𝒪`-modules. -/
  toComplex : CpxO
  /-- The degreewise multiplication map. -/
  mul : ∀ n m : ℤ, toComplex.X n ⊗ toComplex.X m ⟶ toComplex.X (n + m)
  /-- The unit map from the monoidal unit to degree zero. -/
  one : (𝟙_ ModO) ⟶ toComplex.X 0
  /-- Associativity of the multiplication. -/
  mul_assoc :
    ∀ n m k : ℤ,
      (α_ (toComplex.X n) (toComplex.X m) (toComplex.X k)).hom ≫
          (toComplex.X n ◁ mul m k) ≫
          mul n (m + k) =
        (mul n m ▷ toComplex.X k) ≫
          mul (n + m) k ≫
          eqToHom (congrArg toComplex.X (Int.add_assoc n m k))
  /-- The unit acts as a left identity. -/
  one_mul :
    ∀ n : ℤ,
      (λ_ (toComplex.X n)).hom =
        (one ▷ toComplex.X n) ≫
          mul 0 n ≫
          eqToHom (congrArg toComplex.X (zero_add n))
  /-- The unit acts as a right identity. -/
  mul_one :
    ∀ n : ℤ,
      (ρ_ (toComplex.X n)).hom =
        (toComplex.X n ◁ one) ≫
          mul n 0 ≫
          eqToHom (congrArg toComplex.X (add_zero n))
  /-- Compatibility of the differential with multiplication. -/
  d_mul :
    ∀ n m : ℤ,
      mul n m ≫ toComplex.d (n + m) (n + m + 1) =
        ((toComplex.d n (n + 1)) ▷ toComplex.X m) ≫
          mul (n + 1) m ≫
          eqToHom
            (congrArg toComplex.X
              ((Int.add_assoc n 1 m).trans
                ((congrArg (fun p : ℤ ↦ n + p) (Int.add_comm 1 m)).trans
                  (Int.add_assoc n m 1).symm))) +
        n.negOnePow •
          ((toComplex.X n ◁ toComplex.d m (m + 1)) ≫
            mul n (m + 1) ≫
            eqToHom
              (congrArg toComplex.X
                (Int.add_assoc n m 1).symm))

namespace DifferentialGradedAlgebra

/-- Scoped notation for differential graded algebra sheaves over a commutative ring sheaf. -/
scoped syntax:max "DGA(" term ")" : term

scoped macro_rules
  | `(DGA($O)) =>
    `(_root_.SheafOfModules.RingedSite.DifferentialGradedAlgebra (𝒪 := $O))

/-- The canonical coefficient-universe category of module sheaves used by differential graded
algebras and their monoidal constructions. -/
@[stacks 0FRF "ambient module category for differential graded algebras"]
abbrev moduleCategory :=
  ringedSiteModuleCategory.{u, v, w, w} J 𝒪

end DifferentialGradedAlgebra

open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

/-- A differential graded algebra sheaf coerces to its underlying cochain complex. -/
instance instCoeOutDifferentialGradedAlgebra :
    CoeOut DGA(𝒪) CpxO where
  coe 𝒜 := 𝒜.toComplex

namespace DifferentialGradedAlgebra

/-- The underlying integer-graded object of a differential graded algebra, obtained by forgetting
its differential while retaining every homogeneous component. -/
abbrev toGradedObject (A : DGA(𝒪)) : GradedObject ℤ ModO :=
  A.toComplex.X

/-- Evaluation of the underlying graded object recovers the corresponding homogeneous part. -/
@[simp]
theorem toGradedObject_apply (A : DGA(𝒪)) (n : ℤ) :
    A.toGradedObject n = A.toComplex.X n := sorry

/-- A differential graded algebra sheaf evaluates degreewise on its underlying cochain complex. -/
instance instCoeFun : CoeFun DGA(𝒪) (fun _ ↦ ℤ → ModO) where
  coe A := A.toComplex.X

/-- Coercion of a differential graded algebra sheaf recovers its degree-`n` component. -/
@[simp]
theorem coe_apply (A : DGA(𝒪)) (n : ℤ) :
    A n = A.toComplex.X n := sorry

/-- The underlying cochain complex evaluates to the degree-`n` component of the algebra sheaf. -/
@[simp]
theorem toComplex_X (A : DGA(𝒪)) (n : ℤ) :
    A.toComplex.X n = A n := sorry

/-- Definition 24.12.1 (2): a homomorphism of differential graded `𝒪`-algebra sheaves is a
morphism of cochain complexes that preserves the unit and multiplication. -/
@[stacks 0FRF, ext]
structure Hom (A B : DGA(𝒪)) where
  /-- The underlying morphism of cochain complexes. -/
  hom : A.toComplex ⟶ B.toComplex
  /-- The degree-zero component preserves the unit map. -/
  comm_one : A.one ≫ hom.f 0 = B.one
  /-- The degreewise components commute with multiplication. -/
  comm_mul :
    ∀ n m : ℤ,
      A.mul n m ≫ hom.f (n + m) =
        ((hom.f n) ▷ A.toComplex.X m) ≫
          (B.toComplex.X n ◁ hom.f m) ≫
          B.mul n m

/-- A differential graded algebra homomorphism coerces to its underlying cochain map. -/
instance instCoeOutHom {A B : DGA(𝒪)} :
    CoeOut (Hom A B) (A.toComplex ⟶ B.toComplex) where
  coe f := f.hom

/-- A differential graded algebra homomorphism evaluates degreewise. -/
instance instCoeFunHom {A B : DGA(𝒪)} :
    CoeFun (Hom A B) (fun _ ↦ ∀ n : ℤ, A n ⟶ B n) where
  coe f := f.hom.f

/-- Coercion of a differential graded algebra homomorphism recovers its degree-`n` component. -/
@[simp]
theorem hom_coe_apply {A B : DGA(𝒪)} (f : Hom A B) (n : ℤ) :
    f n = f.hom.f n := sorry

/-- The cochain-map component of a differential graded algebra homomorphism is its degreewise
component. -/
@[simp]
theorem hom_f {A B : DGA(𝒪)} (f : Hom A B) (n : ℤ) :
    f.hom.f n = f n := sorry

namespace Hom

/-- The identity homomorphism of a differential graded algebra sheaf. -/
def id (A : DGA(𝒪)) : Hom A A where
  hom := 𝟙 A.toComplex
  comm_one := sorry
  comm_mul := sorry

/-- The composite of differential graded algebra homomorphisms. -/
def comp {A B D : DGA(𝒪)} (f : Hom A B) (g : Hom B D) : Hom A D where
  hom := f.hom ≫ g.hom
  comm_one := sorry
  comm_mul := sorry

/-- The underlying cochain map of the identity homomorphism is the identity. -/
@[simp]
theorem id_hom (A : DGA(𝒪)) : (id A).hom = 𝟙 A.toComplex := sorry

/-- The underlying cochain map of a composite is the composite of underlying cochain maps. -/
@[simp]
theorem comp_hom {A B D : DGA(𝒪)} (f : Hom A B) (g : Hom B D) :
    (comp f g).hom = f.hom ≫ g.hom := sorry

end Hom

/-- Two differential graded algebra homomorphisms are equal when their underlying cochain maps
agree. -/
@[ext]
theorem hom_ext {A B : DGA(𝒪)} (f g : Hom A B) (h : f.hom = g.hom) : f = g := sorry

/-- The underlying cochain map determines a differential graded algebra homomorphism. -/
theorem hom_injective {A B : DGA(𝒪)} : Function.Injective (fun f : Hom A B ↦ f.hom) := sorry

/-- Differential graded algebra sheaves and their homomorphisms form a category. -/
instance instCategory : Category DGA(𝒪) where
  Hom A B := Hom A B
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Forget the multiplication and unit of a differential graded algebra sheaf. -/
def forgetToComplex : DGA(𝒪) ⥤ CpxO where
  obj A := A.toComplex
  map f := f.hom
  map_id := sorry
  map_comp := sorry

/-- Forgetting a differential graded algebra sheaf recovers its underlying cochain complex. -/
@[simp]
theorem forgetToComplex_obj (A : DGA(𝒪)) :
    forgetToComplex.obj A = A.toComplex := sorry

/-- Forgetting a differential graded algebra homomorphism recovers its underlying cochain map. -/
@[simp]
theorem forgetToComplex_map {A B : DGA(𝒪)} (f : A ⟶ B) :
    forgetToComplex.map f = f.hom := sorry

/-- The degree-`n` component of a forgotten differential graded algebra map is its original
degree-`n` component. -/
@[simp]
theorem forgetToComplex_map_f {A B : DGA(𝒪)} (f : A ⟶ B) (n : ℤ) :
    (forgetToComplex.map f).f n = f.hom.f n := sorry

/-- Forgetting to cochain complexes is faithful. -/
instance forgetToComplex_faithful :
    Functor.Faithful (forgetToComplex (J := J) (𝒪 := 𝒪)) where
  map_injective := sorry

/-- The unit of a differential graded algebra sheaf viewed as a map from the structure module,
using its canonical identification with the ambient monoidal unit. -/
abbrev oneFromUnitModule (A : DGA(𝒪)) : unitModule J 𝒪 ⟶ A.toComplex.X 0 :=
  unitIsoTensorUnit.hom ≫ A.one

end DifferentialGradedAlgebra

end

end SheafOfModules.RingedSite
