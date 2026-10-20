module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.Filtration.Morphism.PageRepresentatives
public import ReasLib.CategoryTheory.Subobject.Quotient.Intersection

/-!
# Page Representatives of a Filtered Complex

This file defines the cycle, boundary, and quotient representatives of a finite spectral-sequence
page. It also records the representation-independent conditions for page differentials and maps
induced by filtered-complex morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- The representative in `(K.X n).obj` of the page-cycle object. -/
@[stacks 012M "finite-page cycle representative"]
abbrev Page.Representative.cycle (K : FilteredComplex C) (r : ℕ) (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (K.d n (n + 1)).cycleRepresentative r p

/-- The strict part of the page-cycle representative, before adjoining the filtration-negligible
summand in degree `p + 1`. -/
@[stacks 012M "strict finite-page cycle representative"]
abbrev Page.Representative.strictCycle (K : FilteredComplex C) (r : ℕ) (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  FilteredObject.Hom.Page.strictCycle (K.d n (n + 1)) r p

/-- The representative in `(K.X n).obj` of the page-boundary object. -/
@[stacks 012M "finite-page boundary representative"]
abbrev Page.Representative.boundary (K : FilteredComplex C) (r : ℕ) (n p : ℤ) :
    Subobject ((K.X n).obj) :=
  (K.d (n - 1) n).boundaryRepresentative r p

/-- The page-boundary representative is contained in the page-cycle representative. -/
@[stacks 012M "finite-page boundary containment"]
theorem Page.Representative.boundary_le_cycle
    (K : FilteredComplex C) (r : ℕ) (n p : ℤ) :
    Page.Representative.boundary K r n p ≤ Page.Representative.cycle K r n p := sorry

/-- The explicit page object attached to a filtered complex, represented canonically as
`Zᵣ / (Bᵣ ⊓ Zᵣ)`. The theorem `Page.Representative.boundary_le_cycle` identifies this with the
textbook quotient `Zᵣ / Bᵣ` without making the object depend on an unfinished proof. -/
@[stacks 012M "finite-page quotient representative"]
noncomputable abbrev Page.Representative.quotient (K : FilteredComplex C) (r : ℕ) (n p : ℤ) : C :=
  FilteredObject.Hom.Page.quotient (K.d (n - 1) n) (K.d n (n + 1)) r p

/-- The canonical quotient map from the cycle representative to
`Page.Representative.quotient K r n p`. -/
@[stacks 012M "finite-page quotient projection"]
noncomputable abbrev Page.Representative.toQuotient (K : FilteredComplex C) (r : ℕ) (n p : ℤ) :
    (Page.Representative.cycle K r n p : C) ⟶ Page.Representative.quotient K r n p :=
  FilteredObject.Hom.Page.toQuotient (K.d (n - 1) n) (K.d n (n + 1)) r p

/-- The proof-free page representative is isomorphic to the textbook quotient `Zᵣ / Bᵣ`. -/
@[stacks 012M "finite-page quotient comparison"]
theorem Page.Representative.quotient_isIsomorphic (K : FilteredComplex C) (r : ℕ) (n p : ℤ) :
    IsIsomorphic (Page.Representative.quotient K r n p)
      (cokernel (Subobject.ofLE
        (Page.Representative.boundary K r n p)
        (Page.Representative.cycle K r n p)
        (Page.Representative.boundary_le_cycle K r n p))) := sorry

/-- Reindexing the representative quotient at the successor total degree identifies its
preceding differential with the differential in degree `n`. -/
@[stacks 012M "successor reindexing of a finite-page quotient representative"]
theorem Page.Representative.quotient_succ (K : FilteredComplex C) (r : ℕ) (n p : ℤ) :
    Page.Representative.quotient K r (n + 1) (p + r) =
      FilteredObject.Hom.Page.quotient (K.d n (n + 1)) (K.d (n + 1) (n + 2)) r (p + r) := sorry

/-- A page differential is represented on strict cycles when its quotient action is induced by
the raw differential after discarding the filtration-negligible source summand. The target is
written in the natural successor total degree; internally it is reindexed to the generic
composable-pair quotient through `Page.Representative.quotient_succ`. -/
@[stacks 012M "strict-cycle representation of a finite-page differential"]
def Page.Differential.IsRepresented (K : FilteredComplex C) (r : ℕ) (n p : ℤ)
    (δ : Page.Representative.quotient K r n p ⟶
      Page.Representative.quotient K r (n + 1) (p + r)) : Prop :=
  FilteredObject.Hom.Page.Differential.IsRepresented
    (f0 := K.d (n - 1) n) (f1 := K.d n (n + 1)) (f2 := K.d (n + 1) (n + 2)) r p
    (δ ≫ eqToHom (Page.Representative.quotient_succ K r n p))

namespace Page.Differential.IsRepresented

/-- A strict-cycle represented page differential of a filtered complex is unique. -/
@[stacks 012M "uniqueness of a strict-cycle represented finite-page differential"]
theorem unique
    {K : FilteredComplex C} {r : ℕ} {n p : ℤ}
    {δ ε : Page.Representative.quotient K r n p ⟶
      Page.Representative.quotient K r (n + 1) (p + r)}
    (hδ : Page.Differential.IsRepresented K r n p δ)
    (hε : Page.Differential.IsRepresented K r n p ε) :
    δ = ε := sorry

/-- The two adjacent square-zero equations of a filtered complex supply a finite-page
differential in the strict-cycle representation. This proposition does not choose the map as
non-Prop data. -/
@[stacks 012M "existence of a strict-cycle represented finite-page differential"]
theorem existsMap (K : FilteredComplex C) (r : ℕ) (n p : ℤ) :
    ∃ δ : Page.Representative.quotient K r n p ⟶
      Page.Representative.quotient K r (n + 1) (p + r),
      Page.Differential.IsRepresented K r n p δ := sorry

/-- The strict-cycle represented finite-page differential of a filtered complex is unique. -/
@[stacks 012M "unique existence of a strict-cycle represented finite-page differential"]
theorem existsUniqueMap (K : FilteredComplex C) (r : ℕ) (n p : ℤ) :
    ∃! δ : Page.Representative.quotient K r n p ⟶
      Page.Representative.quotient K r (n + 1) (p + r),
      Page.Differential.IsRepresented K r n p δ := sorry

end Page.Differential.IsRepresented

/-- A map between explicit page representatives is induced by a filtered-complex morphism when
its degree-`n` component induces the corresponding generic map of a composable filtered pair. -/
@[stacks 012M "finite-page morphism inducedness"]
def Page.Map.IsInduced {K L : FilteredComplex C} (α : K ⟶ L) (r : ℕ) (n p : ℤ)
    (γ : Page.Representative.quotient K r n p ⟶ Page.Representative.quotient L r n p) : Prop :=
  FilteredObject.Hom.Page.Map.IsInduced
    (f0 := K.d (n - 1) n) (f1 := K.d n (n + 1))
    (g0 := L.d (n - 1) n) (g1 := L.d n (n + 1))
    (α.f n) r p γ

namespace Page.Map

/-- A morphism of filtered complexes maps source page-cycle representatives into target
page-cycle representatives. This is the filtered-complex bridge to
`FilteredObject.Hom.Page.Map.cycle_factors`. -/
@[stacks 012M "filtered-complex morphism cycle factorization"]
theorem cycle_factors
    {K L : FilteredComplex C} (α : K ⟶ L) (r : ℕ) (n p : ℤ) :
    (Page.Representative.cycle L r n p).Factors
      ((Page.Representative.cycle K r n p).arrow ≫ (α.f n).hom) := sorry

/-- A morphism of filtered complexes maps source boundary-cycle intersections into target
boundary-cycle intersections. This is the filtered-complex bridge to the two-square generic
factorization theorem. -/
@[stacks 012M "filtered-complex morphism intersection factorization"]
theorem intersection_factors
    {K L : FilteredComplex C} (α : K ⟶ L) (r : ℕ) (n p : ℤ) :
    (Page.Representative.boundary L r n p ⊓ Page.Representative.cycle L r n p).Factors
      ((Page.Representative.boundary K r n p ⊓
        Page.Representative.cycle K r n p).arrow ≫ (α.f n).hom) := sorry

end Page.Map

namespace Page.Map.IsInduced

/-- The identity of an explicit page representative is induced by the identity map of the
filtered complex. -/
@[stacks 012M "identity map of explicit page representatives"]
theorem id (K : FilteredComplex C) (r : ℕ) (n p : ℤ) :
    Page.Map.IsInduced (𝟙 K) r n p
      (𝟙 (Page.Representative.quotient K r n p)) := sorry

/-- Maps of explicit page representatives induced by filtered-complex maps are closed under
composition. -/
@[stacks 012M "composition of explicit page representative maps"]
theorem comp {K L M : FilteredComplex C} {α : K ⟶ L} {β : L ⟶ M}
    {r : ℕ} {n p : ℤ}
    {γ : Page.Representative.quotient K r n p ⟶ Page.Representative.quotient L r n p}
    {δ : Page.Representative.quotient L r n p ⟶ Page.Representative.quotient M r n p}
    (hγ : Page.Map.IsInduced α r n p γ) (hδ : Page.Map.IsInduced β r n p δ) :
    Page.Map.IsInduced (α ≫ β) r n p (γ ≫ δ) := sorry

/-- Two explicit page-quotient maps induced by the same filtered-complex morphism are equal. -/
@[stacks 012M "uniqueness of finite-page quotient maps of filtered-complex morphisms"]
theorem unique {K L : FilteredComplex C} {α : K ⟶ L} {r : ℕ} {n p : ℤ}
    {γ δ : Page.Representative.quotient K r n p ⟶ Page.Representative.quotient L r n p}
    (hγ : Page.Map.IsInduced α r n p γ) (hδ : Page.Map.IsInduced α r n p δ) :
    γ = δ := sorry

/-- Every morphism of filtered complexes induces a map between the corresponding explicit
finite-page representatives. This statement avoids selecting morphism data from deferred
factorization proofs. -/
@[stacks 012M "existence of finite-page quotient maps of filtered-complex morphisms"]
theorem existsMap {K L : FilteredComplex C} (α : K ⟶ L) (r : ℕ) (n p : ℤ) :
    ∃ γ : Page.Representative.quotient K r n p ⟶ Page.Representative.quotient L r n p,
      Page.Map.IsInduced α r n p γ := sorry

/-- The explicit finite-page map induced by a morphism of filtered complexes is unique. -/
@[stacks 012M "unique existence of finite-page quotient maps of filtered-complex morphisms"]
theorem existsUniqueMap {K L : FilteredComplex C} (α : K ⟶ L) (r : ℕ) (n p : ℤ) :
    ∃! γ : Page.Representative.quotient K r n p ⟶ Page.Representative.quotient L r n p,
      Page.Map.IsInduced α r n p γ := sorry

end Page.Map.IsInduced

end FilteredComplex

end CategoryTheory
