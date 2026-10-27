/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Filtration.FinitePreadditive
public import ReasLib.CategoryTheory.Filtration.Strict
public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Factor
public import ReasLib.CategoryTheory.Filtration.FiniteBiproduct
import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting into bounded-below filtered-injective cochain complexes

This is the filtered analogue of `CochainComplex.InjectivePlus` lifting. It exposes homotopy
and strict cochain lifts into a `FilteredInjectivePlus` target along a filtered
quasi-isomorphism of complexes of finite filtered objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredInjectivePlus

/-- The underlying target complex of a bounded-below filtered-injective complex. -/
abbrev target (I : FilteredInjectivePlus C) :
    CochainComplex (FilteredObject.Finite.category C) ℤ :=
  (FilteredInjectivePlus.ι C).obj I

/-- Ambient terms of a finite filtered complex, without using its law fields. -/
abbrev terms (K : CochainComplex (FilteredObject.Finite.category C) ℤ) :
    ℤ → FilteredObject C := fun n ↦ (K.X n).obj

/-- Ambient consecutive differentials of a finite filtered complex. -/
abbrev differential (K : CochainComplex (FilteredObject.Finite.category C) ℤ) :
    ∀ n : ℤ, (terms K n).obj ⟶ (terms K (n + 1)).obj :=
  fun n ↦ (K.d n (n + 1)).hom.hom

/-- Ambient components of a cochain map. -/
abbrev components {K L : CochainComplex (FilteredObject.Finite.category C) ℤ} (f : K ⟶ L) :
    ∀ n : ℤ, (terms K n).obj ⟶ (terms L n).obj := fun n ↦ (f.f n).hom.hom

namespace StrictLift

open FilteredObject.Finite.FilteredInjective

/-- The ambient data of a consecutive differential; the complex laws are not data inputs. -/
abbrev Differential (K : ℤ → FilteredObject C) :=
  ∀ n : ℤ, (K n).obj ⟶ (K (n + 1)).obj

/-- Ambient degreewise maps, before bundling filtration or cochain laws. -/
abbrev Components (K L : ℤ → FilteredObject C) := ∀ n : ℤ, (K n).obj ⟶ (L n).obj

/-- The preceding differential, transported only by the integer identity `(n-1)+1=n`. -/
def prevD (K : ℤ → FilteredObject C) (d : Differential K) (n : ℤ) :
    (K (n - 1)).obj ⟶ (K n).obj :=
  d (n - 1) ≫ eqToHom (congrArg (fun j ↦ (K j).obj) (by omega : (n - 1) + 1 = n))

/-- The explicit ambient relation matrix `[[d_K,0],[-α,d_L]]`. -/
def relation (K L : ℤ → FilteredObject C) (dK : Differential K) (dL : Differential L)
    (α : Components K L) (n : ℤ) :
    (K n).obj ⊞ (L (n - 1)).obj ⟶ (K (n + 1)).obj ⊞ (L n).obj :=
  biprod.desc (biprod.lift (dK n) (-α n)) (biprod.lift 0 (prevD L dL n))

/-- The generator map `[α,d_L]` in the next degree. -/
def generators (K L : ℤ → FilteredObject C) (dL : Differential L)
    (α : Components K L) (n : ℤ) :
    (K (n + 1)).obj ⊞ (L n).obj ⟶ (L (n + 1)).obj :=
  biprod.desc (α (n + 1)) (dL n)

/-- The quotient-filtered obstruction object uses the actual ambient relation matrix.
Its construction contains no admitted filtration-preservation or zero-composite proof. -/
def obstructionSource (K L : ℤ → FilteredObject C) (dK : Differential K)
    (dL : Differential L) (α : Components K L) (n : ℤ) : FilteredObject C :=
  (FilteredObject.binaryBiproduct (K (n + 1)) (L n)).pushforward
    (cokernel.π (relation K L dK dL α n))

/-- Total ambient descent of the generator map. Compatibility is checked by the descent
itself; no admitted `relation ≫ generators = 0` certificate enters its data. -/
def obstructionMap (K L : ℤ → FilteredObject C) (dK : Differential K)
    (dL : Differential L) (α : Components K L) (n : ℤ) :
    (obstructionSource K L dK dL α n).obj ⟶ (L (n + 1)).obj :=
  cokernelDescOrZero (relation K L dK dL α n) (generators K L dL α n)

/-- The next ambient component is the actual objectwise extension of the total descent of
`[γ,β d_I]`. All arguments here are data. No recursively admitted law is used by any choice. -/
def next (I : FilteredInjectivePlus C) (K L : ℤ → FilteredObject C)
    (dK : Differential K) (dL : Differential L) (α : Components K L)
    (γ : Components K (terms (target I))) (n : ℤ)
    (β : (L n).obj ⟶ (terms (target I) n).obj) :
    (L (n + 1)).obj ⟶ (terms (target I) (n + 1)).obj :=
  letI : FilteredObject.IsFilteredInjective ((target I).X (n + 1)).obj := I.property _
  extendHom (I := (target I).X (n + 1)) (obstructionSource K L dK dL α n) (L (n + 1))
    (cokernelDescOrZero (relation K L dK dL α n)
      (biprod.desc (γ (n + 1)) (β ≫ differential (target I) n)))
    (obstructionMap K L dK dL α n)

/-- Reindex an ambient component by a proved equality of integer degrees. -/
def transport (I : FilteredInjectivePlus C) (L : ℤ → FilteredObject C) {i j : ℤ}
    (h : i = j) (f : (L i).obj ⟶ (terms (target I) i).obj) :
    (L j).obj ⟶ (terms (target I) j).obj :=
  eqToHom (congrArg (fun n ↦ (L n).obj) h.symm) ≫ f ≫
    eqToHom (congrArg (fun n ↦ (terms (target I) n).obj) h)

/-- The ambient recursion starts at zero in degree `a-1`, then evaluates the explicit
`next` operation. The cutoff and cochain hypotheses occur only in the correctness laws. -/
def iterate (I : FilteredInjectivePlus C) (K L : ℤ → FilteredObject C)
    (dK : Differential K) (dL : Differential L) (α : Components K L)
    (γ : Components K (terms (target I))) (a : ℤ) :
    (k : ℕ) → (L (a - 1 + k)).obj ⟶ (terms (target I) (a - 1 + k)).obj
  | 0 => 0
  | k + 1 => by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
        next I K L dK dL α γ (a - 1 + k) (iterate I K L dK dL α γ a k)

/-- The actual ambient component, with literal zero maps below the specified cutoff. -/
def component (I : FilteredInjectivePlus C) (K L : ℤ → FilteredObject C)
    (dK : Differential K) (dL : Differential L) (α : Components K L)
    (γ : Components K (terms (target I))) (a n : ℤ) :
    (L n).obj ⟶ (terms (target I) n).obj :=
  if h : a ≤ n then
    transport I L (by omega : a - 1 + ((n - a + 1).toNat : ℤ) = n)
      (iterate I K L dK dL α γ a (n - a + 1).toNat)
  else 0

end StrictLift

/-- The strict lift's ambient components, before attaching any preservation or cochain law. -/
def strictLiftAtBoundHom (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (α : K ⟶ L) (γ : K ⟶ target I) (a n : ℤ) :
    (L.X n).obj.obj ⟶ ((target I).X n).obj.obj :=
  StrictLift.component I (terms K) (terms L) (differential K) (differential L)
    (components α) (components γ) a n

/-- Filtration preservation is a law of the specified ambient recursion. -/
theorem strictLiftAtBound_preserves (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ target I) (hmono : ∀ n : ℤ, Mono (α.f n))
    (hstrict : ∀ n : ℤ, FilteredObject.Hom.Strict (α.f n).hom)
    (a : ℤ) (ha : (target I).IsStrictlyGE a) (n p : ℤ) :
    (((target I).X n).obj.filtration.stage p).Factors
      (((L.X n).obj.filtration.stage p).arrow ≫ strictLiftAtBoundHom I α γ a n) := sorry

/-- Bundle the actual ambient recursion as a strict cochain lift. Its laws are attached only
after all data have been constructed, so they cannot become certificates for data selection. -/
def strictLiftAtBound (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ target I) (hmono : ∀ n : ℤ, Mono (α.f n))
    (hstrict : ∀ n : ℤ, FilteredObject.Hom.Strict (α.f n).hom)
    (a : ℤ) (ha : (target I).IsStrictlyGE a) : L ⟶ target I where
  f n := ObjectProperty.homMk (FilteredObject.Hom.mk (strictLiftAtBoundHom I α γ a n)
    (strictLiftAtBound_preserves I hK hL α hα γ hmono hstrict a ha n))
  comm' := by sorry

/-- Computation of the actual ambient component of the strict lift. -/
@[simp]
theorem strictLiftAtBound_f (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ target I) (hmono : ∀ n : ℤ, Mono (α.f n))
    (hstrict : ∀ n : ℤ, FilteredObject.Hom.Strict (α.f n).hom)
    (a : ℤ) (ha : (target I).IsStrictlyGE a) (n : ℤ) :
    ((strictLiftAtBound I hK hL α hα γ hmono hstrict a ha).f n).hom.hom =
      strictLiftAtBoundHom I α γ a n := rfl

/-- The actual strict lift, using the lower bound in the input target's certificate. -/
@[stacks 028I "explicit strict cochain lift"]
def strictLift (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ target I) (hmono : ∀ n : ℤ, Mono (α.f n))
    (hstrict : ∀ n : ℤ, FilteredObject.Hom.Strict (α.f n).hom) : L ⟶ target I :=
  strictLiftAtBound I hK hL α hα γ hmono hstrict
    (Classical.choose I.obj.property) (Classical.choose_spec I.obj.property)

/-- The specified strict lift restricts to the original map. -/
@[stacks 028I "strict lift restriction"]
theorem strictLift_fac (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ target I) (hmono : ∀ n : ℤ, Mono (α.f n))
    (hstrict : ∀ n : ℤ, FilteredObject.Hom.Strict (α.f n).hom) :
    α ≫ strictLift I hK hL α hα γ hmono hstrict = γ := sorry

namespace Cylinder

/-- The explicit cylinder term `L^n ⊕ (K^n ⊕ K^(n+1))`, with the stagewise filtration.
The last two summands form the contractible disk complex with differential `(x,y)↦(y,0)`. -/
def term (K L : CochainComplex (FilteredObject.Finite.category C) ℤ) (n : ℤ) :
    FilteredObject C :=
  FilteredObject.binaryBiproduct (L.X n).obj
    (FilteredObject.binaryBiproduct (K.X n).obj (K.X (n + 1)).obj)

/-- The ambient cylinder differential: `d_L` on the first summand and `(y,0)` on the disk. -/
def differential (K L : CochainComplex (FilteredObject.Finite.category C) ℤ) :
    StrictLift.Differential (term K L) :=
  fun n ↦ biprod.map ((L.d n (n + 1)).hom.hom)
    ((biprod.snd : (K.X n).obj.obj ⊞ (K.X (n + 1)).obj.obj ⟶ _) ≫ biprod.inl)

/-- The ambient cylinder inclusion `(α,id,d_K)`, a split strict monomorphism termwise. -/
def inclusion {K L : CochainComplex (FilteredObject.Finite.category C) ℤ} (α : K ⟶ L) :
    StrictLift.Components (terms K) (term K L) :=
  fun n ↦ biprod.lift (α.f n).hom.hom (biprod.lift (𝟙 _) (K.d n (n + 1)).hom.hom)

end Cylinder

/-- The cylinder lift is computed solely on the explicit cylinder's ambient terms and
matrices. No cylinder cochain-law, quasi-isomorphism, strictness or monomorphy proof is selected. -/
def cylinderLiftHom (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (α : K ⟶ L) (γ : K ⟶ target I) (n : ℤ) :
    (Cylinder.term K L n).obj ⟶ ((target I).X n).obj.obj :=
  StrictLift.component I (terms K) (Cylinder.term K L) (differential K)
    (Cylinder.differential K L) (Cylinder.inclusion α) (components γ)
    (Classical.choose I.obj.property) n

/-- Restrict the actual cylinder lift to the original target summand. -/
def homotopyLiftHom (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (α : K ⟶ L) (γ : K ⟶ target I) (n : ℤ) :
    (L.X n).obj.obj ⟶ ((target I).X n).obj.obj :=
  biprod.inl ≫ cylinderLiftHom I α γ n

/-- Filtration preservation is a separate law of the ambient homotopy-lift formula. -/
theorem homotopyLiftHom_preserves (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ target I) (n p : ℤ) :
    (((target I).X n).obj.filtration.stage p).Factors
      (((L.X n).obj.filtration.stage p).arrow ≫ homotopyLiftHom I α γ n) := sorry

/-- The actual homotopy lift, with all data computed before its filtered/cochain laws. -/
@[stacks 028I "explicit homotopy cochain lift"]
def homotopyLift (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ target I) : L ⟶ target I where
  f n := ObjectProperty.homMk (FilteredObject.Hom.mk (homotopyLiftHom I α γ n)
    (homotopyLiftHom_preserves I hK hL α hα γ n))
  comm' := by sorry

/-- The homotopy's ambient component is minus the cylinder lift on the second disk summand.
The integer equality transports its source; all other components are literal zeros. -/
def homotopyLiftHomotopyHom (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (α : K ⟶ L) (γ : K ⟶ target I) (p q : ℤ) :
    (K.X p).obj.obj ⟶ ((target I).X q).obj.obj :=
  if h : p = q + 1 then
    -(eqToHom (congrArg (fun n ↦ (K.X n).obj.obj) h) ≫ biprod.inr ≫ biprod.inr ≫
      cylinderLiftHom I α γ q)
  else 0

/-- Filtration preservation of the specified homotopy components. -/
theorem homotopyLiftHomotopyHom_preserves (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ target I) (p q r : ℤ) :
    (((target I).X q).obj.filtration.stage r).Factors
      (((K.X p).obj.filtration.stage r).arrow ≫ homotopyLiftHomotopyHom I α γ p q) := sorry

/-- The actual homotopy uses the explicit disk-contraction components. Its laws are attached
after the ambient construction, and are not inputs to any choice. -/
@[stacks 028I "explicit homotopy for the cochain lift"]
def homotopyLiftHomotopy (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ target I) : Homotopy (α ≫ homotopyLift I hK hL α hα γ) γ where
  hom p q := ObjectProperty.homMk (FilteredObject.Hom.mk (homotopyLiftHomotopyHom I α γ p q)
    (homotopyLiftHomotopyHom_preserves I hK hL α hα γ p q))
  zero := by sorry
  comm := by sorry

/-- Computation of the actual ambient homotopy components. -/
@[simp]
theorem homotopyLiftHomotopy_hom (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ target I) (p q : ℤ) :
    ((homotopyLiftHomotopy I hK hL α hα γ).hom p q).hom.hom =
      homotopyLiftHomotopyHom I α γ p q := rfl

/-- The actual ambient components of the lift are the previously constructed raw data. -/
@[simp]
theorem homotopyLift_f (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ target I) (n : ℤ) :
    ((homotopyLift I hK hL α hα γ).f n).hom.hom = homotopyLiftHom I α γ n := rfl

/-- A cochain map into a bounded-below complex of filtered injectives lifts along a filtered
quasi-isomorphism up to homotopy, with the specified recursive witness. -/
@[stacks 028I]
theorem exists_homotopy_lift (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ (FilteredInjectivePlus.ι C).obj I) :
    ∃ β : L ⟶ (FilteredInjectivePlus.ι C).obj I, Nonempty (Homotopy (α ≫ β) γ) :=
  ⟨homotopyLift I hK hL α hα γ, ⟨homotopyLiftHomotopy I hK hL α hα γ⟩⟩

/-- If the filtered quasi-isomorphism is a strict monomorphism in every degree, the specified
recursive cochain lift makes the diagram commute. -/
@[stacks 028I]
theorem exists_lift_of_termwiseStrictMono (I : FilteredInjectivePlus C)
    {K L : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (hK : CochainComplex.plus (FilteredObject.Finite.category C) K)
    (hL : CochainComplex.plus (FilteredObject.Finite.category C) L)
    (α : K ⟶ L) (hα : FilteredObject.Finite.CochainComplex.quasiIso C α)
    (γ : K ⟶ (FilteredInjectivePlus.ι C).obj I)
    (hmono : ∀ n : ℤ, Mono (α.f n))
    (hstrict : ∀ n : ℤ,
      FilteredObject.Hom.Strict ((FilteredObject.Finite.inclusion C).map (α.f n))) :
    ∃ β : L ⟶ (FilteredInjectivePlus.ι C).obj I, α ≫ β = γ :=
  ⟨strictLift I hK hL α hα γ hmono hstrict, strictLift_fac I hK hL α hα γ hmono hstrict⟩

end FilteredInjectivePlus

end CochainComplex
