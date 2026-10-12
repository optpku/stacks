/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra

/-!
# Graded modules underlying differential graded modules

This leaf owns the tensor-morphism presentation of a graded module over the underlying graded
algebra of a differential graded algebra sheaf. It is kept distinct from the sectionwise
`GradedModuleSheaf` model until a tensor/sectionwise equivalence is available.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

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
-- public `Mod(𝒪)` notation overlapping the established graded-module `Mod(...)` scope; it carries
-- no local choice or instance.
local notation "ModO" => ringedSiteModuleCategory J 𝒪

namespace DifferentialGradedAlgebra

/-- A graded right module over the underlying graded algebra of a differential graded algebra
sheaf, presented by action morphisms in the ambient monoidal category. -/
structure GradedModule (𝒜 : DGA(𝒪)) where
  /-- The module in each degree. -/
  obj : ℤ → ModO
  /-- The degreewise right action. -/
  smul : ∀ n m : ℤ, obj n ⊗ 𝒜.toComplex.X m ⟶ obj (n + m)
  /-- Associativity of the graded action. -/
  smul_assoc :
    ∀ n m k : ℤ,
      (α_ (obj n) (𝒜.toComplex.X m) (𝒜.toComplex.X k)).hom ≫
          (obj n ◁ 𝒜.mul m k) ≫
          smul n (m + k) =
        (smul n m ▷ 𝒜.toComplex.X k) ≫
          smul (n + m) k ≫
          eqToHom (congrArg obj (Int.add_assoc n m k))
  /-- The degree-zero unit acts by the identity. -/
  one_smul :
    ∀ n : ℤ,
      (ρ_ (obj n)).hom =
        (obj n ◁ 𝒜.one) ≫
          smul n 0 ≫
          eqToHom (congrArg obj (add_zero n))

namespace GradedModule

/-- The graded object underlying a graded module in the tensor-morphism presentation. -/
abbrev toGradedObject {𝒜 : DGA(𝒪)} (M : GradedModule 𝒜) : GradedObject ℤ ModO :=
  M.obj

/-- Evaluation of the underlying graded object is evaluation of the stored degreewise family. -/
@[simp]
theorem toGradedObject_apply {𝒜 : DGA(𝒪)} (M : GradedModule 𝒜) (n : ℤ) :
    M.toGradedObject n = M.obj n := sorry

/-- A graded module evaluates to its degreewise family. -/
instance instCoeFun {𝒜 : DGA(𝒪)} :
    CoeFun (GradedModule 𝒜) (fun _ ↦ ℤ → ModO) where
  coe M := M.obj

/-- Evaluation of a graded module is its stored degreewise object. -/
@[simp]
theorem coe_apply {𝒜 : DGA(𝒪)} (M : GradedModule 𝒜) (n : ℤ) :
    M n = M.obj n := sorry

/-- A morphism of graded modules is a degreewise family compatible with the right action. -/
@[ext]
structure Hom {𝒜 : DGA(𝒪)} (M N : GradedModule 𝒜) where
  /-- The map in each degree. -/
  hom : ∀ n : ℤ, M.obj n ⟶ N.obj n
  /-- Compatibility with the graded action. -/
  comm :
    ∀ n m : ℤ,
      M.smul n m ≫ hom (n + m) =
        (hom n ▷ 𝒜.toComplex.X m) ≫ N.smul n m

/-- A graded-module morphism evaluates to its degreewise maps. -/
instance instCoeFunHom {𝒜 : DGA(𝒪)} {M N : GradedModule 𝒜} :
    CoeFun (Hom M N) (fun _ ↦ ∀ n : ℤ, M.obj n ⟶ N.obj n) where
  coe f := f.hom

/-- Evaluation of a graded-module morphism is its stored degreewise map. -/
@[simp]
theorem hom_coe_apply {𝒜 : DGA(𝒪)} {M N : GradedModule 𝒜}
    (f : Hom M N) (n : ℤ) :
    f n = f.hom n := sorry

/-- Degreewise maps determine a graded-module morphism. -/
theorem hom_injective {𝒜 : DGA(𝒪)} {M N : GradedModule 𝒜} :
    Function.Injective (fun f : Hom M N ↦ f.hom) := sorry

namespace Hom

/-- The identity graded-module morphism. -/
def id {𝒜 : DGA(𝒪)} (M : GradedModule 𝒜) : Hom M M where
  hom := fun n ↦ 𝟙 (M.obj n)
  comm := sorry

/-- Composition of graded-module morphisms. -/
def comp {𝒜 : DGA(𝒪)} {M N P : GradedModule 𝒜}
    (f : Hom M N) (g : Hom N P) : Hom M P where
  hom := fun n ↦ f.hom n ≫ g.hom n
  comm := sorry

/-- The identity morphism is degreewise the identity. -/
@[simp]
theorem id_hom {𝒜 : DGA(𝒪)} (M : GradedModule 𝒜) (n : ℤ) :
    (id M).hom n = 𝟙 (M.obj n) := sorry

/-- Composition is computed degreewise. -/
@[simp]
theorem comp_hom {𝒜 : DGA(𝒪)} {M N P : GradedModule 𝒜}
    (f : Hom M N) (g : Hom N P) (n : ℤ) :
    (comp f g).hom n = f.hom n ≫ g.hom n := sorry

end Hom

/-- Graded modules over a fixed differential graded algebra form a category. -/
instance instCategory (𝒜 : DGA(𝒪)) : Category (GradedModule 𝒜) where
  Hom M N := Hom M N
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end GradedModule

end DifferentialGradedAlgebra

end

end SheafOfModules.RingedSite
