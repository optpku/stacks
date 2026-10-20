module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtration.Category
public import ReasLib.CategoryTheory.Subobject.Quotient.Intersection

/-!
# Page Representatives of a Filtered Morphism

The cycle and boundary expressions used by a filtered-complex spectral sequence depend only on
one morphism between filtered objects.  This file owns those morphism-level constructions; a
filtered complex obtains its page representatives by applying them to consecutive differentials.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : FilteredObject C}

/-- The page-`r` cycle representative of a filtered morphism `f : X ⟶ Y` at filtration index
`p`: `(X.filtration.stage p ⊓ (Subobject.pullback f.hom).obj
(Y.filtration.stage (p + r))) ⊔ X.filtration.stage (p + 1)`. -/
@[stacks 012F "cycle representative of a filtered morphism"]
def cycleRepresentative (f : X ⟶ Y) (r : ℕ) (p : ℤ) : Subobject X.obj :=
  (X.filtration.stage p ⊓
      (Subobject.pullback f.hom).obj (Y.filtration.stage (p + r))) ⊔
    X.filtration.stage (p + 1)

/-- The page-`r` boundary representative of a filtered morphism `f : X ⟶ Y` at filtration
index `p`: `(Y.filtration.stage p ⊓ imageSubobject
((X.filtration.stage (p - r + 1)).arrow ≫ f.hom)) ⊔ Y.filtration.stage (p + 1)`. -/
@[stacks 012F "boundary representative of a filtered morphism"]
def boundaryRepresentative (f : X ⟶ Y) (r : ℕ) (p : ℤ) : Subobject Y.obj :=
  (Y.filtration.stage p ⊓
      imageSubobject
        ((X.filtration.stage (p - r + 1)).arrow ≫ f.hom)) ⊔
    Y.filtration.stage (p + 1)

/-- The intrinsic cycle representative `f.kernelRepresentative p`. -/
@[stacks 012F "intrinsic cycle representative of a filtered morphism"]
def kernelRepresentative (f : X ⟶ Y) (p : ℤ) : Subobject X.obj :=
  (kernelSubobject f.hom ⊓ X.filtration.stage p) ⊔ X.filtration.stage (p + 1)

/-- The intrinsic boundary representative `f.imageRepresentative p`. -/
@[stacks 012F "intrinsic boundary representative of a filtered morphism"]
def imageRepresentative (f : X ⟶ Y) (p : ℤ) : Subobject Y.obj :=
  (imageSubobject f.hom ⊓ Y.filtration.stage p) ⊔ Y.filtration.stage (p + 1)

/-! ## Finite-page representatives of a composable pair -/

namespace Page

variable {X0 X1 X2 X3 Y0 Y1 Y2 Y3 Z0 Z1 Z2 : FilteredObject C}

/-- The strict part of the page-`r` cycle representative of `f`, before adjoining the
filtration-negligible summand in degree `p + 1`. -/
@[stacks 012F "strict cycle representative of a filtered morphism"]
def strictCycle (f : X0 ⟶ X1) (r : ℕ) (p : ℤ) : Subobject X0.obj :=
  X0.filtration.stage p ⊓
    (Subobject.pullback f.hom).obj (X1.filtration.stage (p + r))

/-- The page-cycle representative is the strict page-cycle representative together with the
filtration-negligible summand in degree `p + 1`. -/
@[simp, stacks 012F "cycle representative as strict cycle plus filtration"]
theorem cycleRepresentative_eq (f : X0 ⟶ X1) (r : ℕ) (p : ℤ) :
    f.cycleRepresentative r p = strictCycle f r p ⊔ X0.filtration.stage (p + 1) := sorry

/-- The page quotient attached to a composable pair `f, g`, represented as the quotient of the
cycle representative of `g` by its intersection with the boundary representative of `f`. -/
@[stacks 012F "finite-page quotient of a composable filtered pair"]
noncomputable abbrev quotient (f : X0 ⟶ X1) (g : X1 ⟶ X2) (r : ℕ) (p : ℤ) : C :=
  Subobject.intersectionQuotient (f.boundaryRepresentative r p) (g.cycleRepresentative r p)

/-- The canonical projection from the page-cycle representative of `g` to the page quotient of
the composable pair `f, g`. -/
@[stacks 012F "finite-page quotient projection of a composable filtered pair"]
noncomputable abbrev toQuotient (f : X0 ⟶ X1) (g : X1 ⟶ X2) (r : ℕ) (p : ℤ) :
    (g.cycleRepresentative r p : C) ⟶ quotient f g r p :=
  Subobject.IntersectionQuotient.π (f.boundaryRepresentative r p) (g.cycleRepresentative r p)

/-- The canonical map from strict page cycles to the page quotient.  It is the correct source
cover for describing a page differential: the summand `F^(p + 1)` is already killed in the
quotient, so no raw differential on the enlarged cycle representative is required. -/
@[stacks 012F "strict-cycle cover of a finite-page quotient"]
noncomputable def strictCycleToQuotient
    (f : X0 ⟶ X1) (g : X1 ⟶ X2) (r : ℕ) (p : ℤ) :
    (strictCycle g r p : C) ⟶ quotient f g r p :=
  Subobject.ofLE (strictCycle g r p) (g.cycleRepresentative r p)
      (_root_.le_sup_left : strictCycle g r p ≤ g.cycleRepresentative r p) ≫
    toQuotient f g r p

/-- Strict page cycles cover the corresponding page quotient. -/
@[stacks 012F "strict-cycle cover is epi"]
instance strictCycleToQuotient_epi
    (f : X0 ⟶ X1) (g : X1 ⟶ X2) (r : ℕ) (p : ℤ) :
    Epi (strictCycleToQuotient f g r p) := sorry

/-- If two composable filtered morphisms have zero composite, then the boundary representative
of the first is contained in the cycle representative of the second. -/
@[stacks 012F "boundary contained in cycle for a zero composite"]
theorem boundary_le_cycle_of_comp_eq_zero
    (f : X0 ⟶ X1) (g : X1 ⟶ X2) (hzero : f.hom ≫ g.hom = 0)
    (r : ℕ) (p : ℤ) :
    f.boundaryRepresentative r p ≤ g.cycleRepresentative r p := sorry

/-- When a composable pair has zero composite, its proof-free page quotient is isomorphic to
the textbook quotient of the cycle representative by the boundary representative. -/
@[stacks 012F "finite-page quotient comparison for a zero composite"]
theorem quotient_isIsomorphic_of_comp_eq_zero
    (f : X0 ⟶ X1) (g : X1 ⟶ X2) (hzero : f.hom ≫ g.hom = 0)
    (r : ℕ) (p : ℤ) :
    IsIsomorphic (quotient f g r p)
      (cokernel (Subobject.ofLE (f.boundaryRepresentative r p) (g.cycleRepresentative r p)
        (boundary_le_cycle_of_comp_eq_zero f g hzero r p))) := sorry

namespace Cycle

/-- Restrict an ambient morphism to strict page-cycle representatives using a supplied
factorization certificate. -/
@[stacks 012F "map of strict finite-page cycle representatives"]
noncomputable def mapOf
    {f : X0 ⟶ X1} {g : Y0 ⟶ Y1} (a : X0.obj ⟶ Y0.obj)
    (h_factors : (strictCycle g r p).Factors ((strictCycle f r p).arrow ≫ a)) :
    (strictCycle f r p : C) ⟶ (strictCycle g r p : C) :=
  (strictCycle g r p).factorThru ((strictCycle f r p).arrow ≫ a) h_factors

/-- The strict page-cycle map recovers its ambient morphism after the target inclusion. -/
@[reassoc (attr := simp), stacks 012F "naturality of strict finite-page cycle representatives"]
theorem mapOf_arrow
    {f : X0 ⟶ X1} {g : Y0 ⟶ Y1} (a : X0.obj ⟶ Y0.obj)
    (h_factors : (strictCycle g r p).Factors ((strictCycle f r p).arrow ≫ a)) :
    mapOf a h_factors ≫ (strictCycle g r p).arrow = (strictCycle f r p).arrow ≫ a := sorry

end Cycle

namespace Map

/-- Construct a map between page quotients of two composable filtered pairs from a coherent
square between their cycle and boundary-cycle intersection representatives.  The coherence is
an explicit input, so the resulting non-Prop datum does not depend on a deferred proof. -/
@[stacks 012F "map of finite-page quotients of composable filtered pairs"]
noncomputable def map
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {g0 : Y0 ⟶ Y1} {g1 : Y1 ⟶ Y2}
    (intersection :
      ((f0.boundaryRepresentative r p ⊓ f1.cycleRepresentative r p : Subobject X1.obj) : C) ⟶
        ((g0.boundaryRepresentative r p ⊓ g1.cycleRepresentative r p : Subobject Y1.obj) : C))
    (cycle : (f1.cycleRepresentative r p : C) ⟶ (g1.cycleRepresentative r p : C))
    (h_comm :
      Subobject.ofLE (f0.boundaryRepresentative r p ⊓ f1.cycleRepresentative r p)
          (f1.cycleRepresentative r p) _root_.inf_le_right ≫ cycle =
        intersection ≫
          Subobject.ofLE (g0.boundaryRepresentative r p ⊓ g1.cycleRepresentative r p)
            (g1.cycleRepresentative r p) _root_.inf_le_right) :
    quotient f0 f1 r p ⟶ quotient g0 g1 r p :=
  Subobject.IntersectionQuotient.map intersection cycle h_comm

/-- The map of page quotients is characterized by its action on the page-cycle representatives. -/
@[reassoc (attr := simp), stacks 012F "naturality of finite-page quotients of composable filtered pairs"]
theorem π_map
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {g0 : Y0 ⟶ Y1} {g1 : Y1 ⟶ Y2}
    (intersection :
      ((f0.boundaryRepresentative r p ⊓ f1.cycleRepresentative r p : Subobject X1.obj) : C) ⟶
        ((g0.boundaryRepresentative r p ⊓ g1.cycleRepresentative r p : Subobject Y1.obj) : C))
    (cycle : (f1.cycleRepresentative r p : C) ⟶ (g1.cycleRepresentative r p : C))
    (h_comm :
      Subobject.ofLE (f0.boundaryRepresentative r p ⊓ f1.cycleRepresentative r p)
          (f1.cycleRepresentative r p) _root_.inf_le_right ≫ cycle =
        intersection ≫
          Subobject.ofLE (g0.boundaryRepresentative r p ⊓ g1.cycleRepresentative r p)
            (g1.cycleRepresentative r p) _root_.inf_le_right) :
    toQuotient f0 f1 r p ≫ map intersection cycle h_comm =
      cycle ≫ toQuotient g0 g1 r p := sorry

/-- A map between page quotients is induced by a filtered middle morphism when it lifts to the
corresponding cycle representatives and descends through their boundary-cycle intersections. -/
@[stacks 012F "induced map of finite-page quotients of composable filtered pairs"]
def IsInduced
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {g0 : Y0 ⟶ Y1} {g1 : Y1 ⟶ Y2}
    (a : X1 ⟶ Y1) (r : ℕ) (p : ℤ)
    (γ : quotient f0 f1 r p ⟶ quotient g0 g1 r p) : Prop :=
  ∃ cycle : (f1.cycleRepresentative r p : C) ⟶ (g1.cycleRepresentative r p : C),
    cycle ≫ (g1.cycleRepresentative r p).arrow =
      (f1.cycleRepresentative r p).arrow ≫ a.hom ∧
      Subobject.IntersectionQuotient.IsInduced cycle γ

/-- The quotient map built from an explicit coherent square is induced by an ambient filtered
middle morphism when its cycle component is the corresponding restricted ambient map. -/
@[stacks 012F "canonical finite-page quotient map is induced"]
theorem map_isInduced
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {g0 : Y0 ⟶ Y1} {g1 : Y1 ⟶ Y2}
    {a : X1 ⟶ Y1} {r : ℕ} {p : ℤ}
    (intersection :
      ((f0.boundaryRepresentative r p ⊓ f1.cycleRepresentative r p : Subobject X1.obj) : C) ⟶
        ((g0.boundaryRepresentative r p ⊓ g1.cycleRepresentative r p : Subobject Y1.obj) : C))
    (cycle : (f1.cycleRepresentative r p : C) ⟶ (g1.cycleRepresentative r p : C))
    (h_comm :
      Subobject.ofLE (f0.boundaryRepresentative r p ⊓ f1.cycleRepresentative r p)
          (f1.cycleRepresentative r p) _root_.inf_le_right ≫ cycle =
        intersection ≫
          Subobject.ofLE (g0.boundaryRepresentative r p ⊓ g1.cycleRepresentative r p)
            (g1.cycleRepresentative r p) _root_.inf_le_right)
    (cycle_arrow : cycle ≫ (g1.cycleRepresentative r p).arrow =
      (f1.cycleRepresentative r p).arrow ≫ a.hom) :
    IsInduced a r p (map intersection cycle h_comm) := sorry

/-- A commuting square of filtered morphisms preserves strict page-cycle representatives. -/
@[stacks 012F "strict finite-page cycle factorization of a commuting square"]
theorem strictCycle_factors
    {f : X0 ⟶ X1} {g : Y0 ⟶ Y1} {a0 : X0 ⟶ Y0} {a1 : X1 ⟶ Y1}
    (h : CommSq f a0 a1 g) (r : ℕ) (p : ℤ) :
    (strictCycle g r p).Factors ((strictCycle f r p).arrow ≫ a0.hom) := sorry

/-- A commuting square of filtered morphisms preserves page-cycle representatives. -/
@[stacks 012F "finite-page cycle factorization of a commuting square"]
theorem cycle_factors
    {f : X0 ⟶ X1} {g : Y0 ⟶ Y1} {a0 : X0 ⟶ Y0} {a1 : X1 ⟶ Y1}
    (h : CommSq f a0 a1 g) (r : ℕ) (p : ℤ) :
    (g.cycleRepresentative r p).Factors ((f.cycleRepresentative r p).arrow ≫ a0.hom) := sorry

/-- A commuting square of filtered morphisms preserves page-boundary representatives. -/
@[stacks 012F "finite-page boundary factorization of a commuting square"]
theorem boundary_factors
    {f : X0 ⟶ X1} {g : Y0 ⟶ Y1} {a0 : X0 ⟶ Y0} {a1 : X1 ⟶ Y1}
    (h : CommSq f a0 a1 g) (r : ℕ) (p : ℤ) :
    (g.boundaryRepresentative r p).Factors ((f.boundaryRepresentative r p).arrow ≫ a1.hom) := sorry

/-- Two adjacent commuting squares preserve the intersection of the boundary and cycle
representatives in their common middle object. -/
@[stacks 012F "finite-page boundary-cycle intersection factorization"]
theorem intersection_factors
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {g0 : Y0 ⟶ Y1} {g1 : Y1 ⟶ Y2}
    {a0 : X0 ⟶ Y0} {a1 : X1 ⟶ Y1} {a2 : X2 ⟶ Y2}
    (h0 : CommSq f0 a0 a1 g0) (h1 : CommSq f1 a1 a2 g1)
    (r : ℕ) (p : ℤ) :
    (g0.boundaryRepresentative r p ⊓ g1.cycleRepresentative r p).Factors
      ((f0.boundaryRepresentative r p ⊓ f1.cycleRepresentative r p).arrow ≫ a1.hom) := sorry

namespace IsInduced

/-- The identity map of a page quotient is induced by the identity filtered middle morphism. -/
@[stacks 012F "identity map of finite-page quotients of a composable filtered pair"]
theorem id (f0 : X0 ⟶ X1) (f1 : X1 ⟶ X2) (r : ℕ) (p : ℤ) :
    IsInduced (𝟙 X1) r p (𝟙 (quotient f0 f1 r p)) := sorry

/-- Page-quotient maps induced by filtered middle morphisms are closed under composition. -/
@[stacks 012F "composition of induced finite-page quotient maps"]
theorem comp
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2}
    {g0 : Y0 ⟶ Y1} {g1 : Y1 ⟶ Y2}
    {h0 : Z0 ⟶ Z1} {h1 : Z1 ⟶ Z2}
    {a : X1 ⟶ Y1} {b : Y1 ⟶ Z1}
    {r : ℕ} {p : ℤ}
    {γ : quotient f0 f1 r p ⟶ quotient g0 g1 r p}
    {δ : quotient g0 g1 r p ⟶ quotient h0 h1 r p}
    (hγ : IsInduced a r p γ) (hδ : IsInduced b r p δ) :
    IsInduced (a ≫ b) r p (γ ≫ δ) := sorry

/-- Two page-quotient maps induced by the same filtered middle morphism are equal. -/
@[stacks 012F "uniqueness of induced finite-page quotient maps"]
theorem unique
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {g0 : Y0 ⟶ Y1} {g1 : Y1 ⟶ Y2}
    {a : X1 ⟶ Y1} {r : ℕ} {p : ℤ}
    {γ δ : quotient f0 f1 r p ⟶ quotient g0 g1 r p}
    (hγ : IsInduced a r p γ) (hδ : IsInduced a r p δ) :
    γ = δ := sorry

/-- Two adjacent commuting squares supply an induced map between their page quotients.  This
proposition-valued API does not choose quotient-map data from deferred factorization proofs. -/
@[stacks 012F "existence of induced finite-page quotient maps"]
theorem existsMap
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {g0 : Y0 ⟶ Y1} {g1 : Y1 ⟶ Y2}
    {a0 : X0 ⟶ Y0} {a1 : X1 ⟶ Y1} {a2 : X2 ⟶ Y2}
    (h0 : CommSq f0 a0 a1 g0) (h1 : CommSq f1 a1 a2 g1)
    (r : ℕ) (p : ℤ) :
    ∃ γ : quotient f0 f1 r p ⟶ quotient g0 g1 r p, IsInduced a1 r p γ := sorry

/-- The map between page quotients induced by two adjacent commuting squares is unique. -/
@[stacks 012F "unique existence of induced finite-page quotient maps"]
theorem existsUniqueMap
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {g0 : Y0 ⟶ Y1} {g1 : Y1 ⟶ Y2}
    {a0 : X0 ⟶ Y0} {a1 : X1 ⟶ Y1} {a2 : X2 ⟶ Y2}
    (h0 : CommSq f0 a0 a1 g0) (h1 : CommSq f1 a1 a2 g1)
    (r : ℕ) (p : ℤ) :
    ∃! γ : quotient f0 f1 r p ⟶ quotient g0 g1 r p, IsInduced a1 r p γ := sorry

end IsInduced

end Map

namespace Differential

/-- Restrict a middle morphism to strict page-cycle representatives using an explicit
factorization certificate. -/
@[stacks 012F "strict finite-page differential map"]
noncomputable def strictMapOf
    {f : X1 ⟶ X2} {g : X2 ⟶ X3} {r : ℕ} {p : ℤ}
    (h_factors : (strictCycle g r (p + r)).Factors
      ((strictCycle f r p).arrow ≫ f.hom)) :
    (strictCycle f r p : C) ⟶ (strictCycle g r (p + r) : C) :=
  (strictCycle g r (p + r)).factorThru ((strictCycle f r p).arrow ≫ f.hom) h_factors

/-- The strict-cycle differential map recovers the ambient middle morphism after the target
inclusion. -/
@[reassoc (attr := simp), stacks 012F "naturality of a strict finite-page differential map"]
theorem strictMapOf_arrow
    {f : X1 ⟶ X2} {g : X2 ⟶ X3} {r : ℕ} {p : ℤ}
    (h_factors : (strictCycle g r (p + r)).Factors
      ((strictCycle f r p).arrow ≫ f.hom)) :
    strictMapOf h_factors ≫ (strictCycle g r (p + r)).arrow =
      (strictCycle f r p).arrow ≫ f.hom := sorry

/-- A page-quotient morphism is represented by the underlying middle morphism on strict cycle
representatives.  This is the quotient/roof formulation appropriate for page differentials; it
does not require the raw morphism to preserve the enlarged cycle representatives. -/
@[stacks 012F "strict-cycle representation of a finite-page differential"]
def IsRepresented
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {f2 : X2 ⟶ X3}
    (r : ℕ) (p : ℤ)
    (δ : quotient f0 f1 r p ⟶ quotient f1 f2 r (p + r)) : Prop :=
  ∃ h_factors : (strictCycle f2 r (p + r)).Factors
      ((strictCycle f1 r p).arrow ≫ f1.hom),
    strictCycleToQuotient f0 f1 r p ≫ δ =
      strictMapOf h_factors ≫ strictCycleToQuotient f1 f2 r (p + r)

/-- A zero composite makes the middle morphism factor from strict source cycles to strict target
cycles at the shifted filtration degree. -/
@[stacks 012F "strict finite-page differential cycle factorization"]
theorem strictCycle_factors
    {f : X1 ⟶ X2} {g : X2 ⟶ X3} (hzero : f.hom ≫ g.hom = 0)
    (r : ℕ) (p : ℤ) :
    (strictCycle g r (p + r)).Factors ((strictCycle f r p).arrow ≫ f.hom) := sorry

namespace IsRepresented

/-- A page differential represented on strict cycles is uniquely determined. -/
@[stacks 012F "uniqueness of a strict-cycle represented finite-page differential"]
theorem unique
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {f2 : X2 ⟶ X3}
    {r : ℕ} {p : ℤ}
    {δ ε : quotient f0 f1 r p ⟶ quotient f1 f2 r (p + r)}
    (hδ : IsRepresented r p δ) (hε : IsRepresented r p ε) :
    δ = ε := sorry

/-- A pair of consecutive zero-composite conditions supplies a finite-page differential in the
strict-cycle sense.  The result is proposition-valued, so it does not choose morphism data from
deferred proof obligations. -/
@[stacks 012F "existence of a strict-cycle represented finite-page differential"]
theorem existsMap
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {f2 : X2 ⟶ X3}
    (hzero0 : f0.hom ≫ f1.hom = 0) (hzero1 : f1.hom ≫ f2.hom = 0)
    (r : ℕ) (p : ℤ) :
    ∃ δ : quotient f0 f1 r p ⟶ quotient f1 f2 r (p + r), IsRepresented r p δ := sorry

/-- The strict-cycle represented finite-page differential is uniquely determined when the two
adjacent composites vanish. -/
@[stacks 012F "unique existence of a strict-cycle represented finite-page differential"]
theorem existsUniqueMap
    {f0 : X0 ⟶ X1} {f1 : X1 ⟶ X2} {f2 : X2 ⟶ X3}
    (hzero0 : f0.hom ≫ f1.hom = 0) (hzero1 : f1.hom ≫ f2.hom = 0)
    (r : ℕ) (p : ℤ) :
    ∃! δ : quotient f0 f1 r p ⟶ quotient f1 f2 r (p + r), IsRepresented r p δ := sorry

end IsRepresented

end Differential

end Page

section CycleLimitRepresentatives

variable [LocallySmall.{v} C] [WellPowered.{v} C] [HasWidePullbacks.{v} C]

/-- The eventual cycle representative, characterized as the infimum of all finite cycle
representatives. -/
@[stacks 012I "canonical eventual cycle representative"]
noncomputable def eventualCycleRepresentative (f : X ⟶ Y) (p : ℤ) : Subobject X.obj :=
  Subobject.sInf.{v} (Set.range fun r : ℕ ↦ f.cycleRepresentative r p)

namespace Representative

namespace Cycle

/-- Intrinsic cycles are contained in the eventual cycle representative. -/
@[stacks 012S "intrinsic cycles lie in every eventual cycle stage"]
theorem kernel_le_eventual (f : X ⟶ Y) (p : ℤ) :
    f.kernelRepresentative p ≤ f.eventualCycleRepresentative p := sorry

end Cycle

end Representative

end CycleLimitRepresentatives

section BoundaryLimitRepresentatives

variable [LocallySmall.{v} C] [WellPowered.{v} C] [HasCoproducts.{v} C]

/-- The eventual boundary representative, characterized as the supremum of all finite boundary
representatives. -/
@[stacks 012I "canonical eventual boundary representative"]
noncomputable def eventualBoundaryRepresentative (f : X ⟶ Y) (p : ℤ) : Subobject Y.obj :=
  Subobject.sSup.{v} (Set.range fun r : ℕ ↦ f.boundaryRepresentative r p)

namespace Representative

namespace Boundary

/-- The eventual boundary representative is contained in the intrinsic boundary
representative. -/
@[stacks 012T "eventual boundaries lie in the intrinsic boundary stage"]
theorem eventual_le_image (f : X ⟶ Y) (p : ℤ) :
    f.eventualBoundaryRepresentative p ≤ f.imageRepresentative p := sorry

end Boundary

end Representative

end BoundaryLimitRepresentatives

end FilteredObject.Hom

end CategoryTheory
