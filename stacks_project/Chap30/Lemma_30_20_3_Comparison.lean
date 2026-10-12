/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealPower
public import ReasLib.Algebra.Module.IdealPower.Submodule.Tensor
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism

/-!
# Ideal-power comparison for cohomology over an affine base

This module packages the inverse systems `H^p(X, I^n F)` and `I^n H^p(X, F)`, the
Rees multiplication map, and the shifted comparison data of Stacks tag 02OA.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology

variable {A : Type u} [CommRing A]
variable {X : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- Affine-base cohomology carries its `A`-module structure from `ModuleCat A`. -/
instance module_cohomology (f : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) (p : ℕ) :
    Module A (Hom.cohomology f F p) :=
  ModuleCat.isModule (Hom.cohomology f F p)

/-- Affine-base cohomology is an abelian group via its `ModuleCat` carrier. -/
instance addCommGroup_cohomology (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) :
    AddCommGroup (Hom.cohomology f F p) :=
  ModuleCat.isAddCommGroup (Hom.cohomology f F p)

/-- The sheaf `I^n F` obtained by applying the pullback of `I` along `f`. -/
noncomputable abbrev product (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (n : ℕ) : X.Modules :=
  (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F n : X.Modules)

/-- The product at exponent `n` is the existing ideal-power product subobject. -/
theorem product_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (n : ℕ) :
    product I f F n =
      (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F n :
        X.Modules) := sorry

/-- The inclusion `I^(n+1) F ⟶ I^n F` of consecutive ideal-power products. -/
noncomputable def productStep (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (n : ℕ) :
    product I f F (n + 1) ⟶ product I f F n :=
  Subobject.ofLE
    (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F (n + 1))
    (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F n)
    (IdealPowerProduct.antitone ((idealSheafDataOfIdealOnSpec I).comap f) F n)

/-- Consecutive product inclusions compose with the shallower subobject arrow. -/
theorem productStep_comp_arrow (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (n : ℕ) :
    productStep I f F n ≫
        (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F n).arrow =
      (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F (n + 1)).arrow :=
  sorry

/-- The cohomology object `H^p(X, I^n F)` as an `A`-module. -/
noncomputable abbrev stage (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) : ModuleCat A :=
  Hom.cohomology f (product I f F n) p

/-- Stage cohomology is affine-base cohomology of the corresponding product. -/
theorem stage_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    stage I f F p n = Hom.cohomology f (product I f F n) p := sorry

/-- The successor transition on `H^p(X, I^n F)`. -/
noncomputable def step (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    stage I f F p (n + 1) ⟶ stage I f F p n :=
  (Hom.cohomologyFunctor f p).map (productStep I f F n)

/-- The inverse system `n ↦ H^p(X, I^n F)`. -/
noncomputable def tower (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) : SequentialInverseSystem (ModuleCat A) :=
  Functor.ofOpSequence (fun n ↦ step I f F p n)

/-- The object at index `n` of the ideal-power cohomology tower. -/
theorem tower_obj (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    (tower I f F p).obj (op n) = stage I f F p n := sorry

/-- Every successor transition of the cohomology tower is `step`. -/
theorem tower_stepMap (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    (tower I f F p).stepMap n = step I f F p n := sorry

/-- The canonical transition `H^p(X, I^n F) ⟶ H^p(X, I^m F)` for `m ≤ n`. -/
noncomputable def transition (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    stage I f F p n ⟶ stage I f F p m :=
  (tower I f F p).transitionMap h

/-- Every tower transition is the named cohomology transition. -/
theorem tower_transitionMap (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    (tower I f F p).transitionMap h = transition I f F p h := sorry

/-- The canonical map `H^p(X, I^n F) ⟶ H^p(X, F)` induced by the product inclusion. -/
noncomputable def toAmbient (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    stage I f F p n ⟶ Hom.cohomology f F p :=
  (Hom.cohomologyFunctor f p).map
    (idealPowerProductSubobject ((idealSheafDataOfIdealOnSpec I).comap f) F n).arrow

/-- Stage transitions commute with the maps to ambient cohomology. -/
theorem step_comp_toAmbient (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    step I f F p n ≫ toAmbient I f F p n = toAmbient I f F p (n + 1) := sorry

/-- The `n`th ideal-power submodule of ambient cohomology, as an `A`-module. -/
noncomputable abbrev ambientStage (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) : ModuleCat A :=
  Ideal.PowerSubmodule.stageObj I (Hom.cohomology f F p) n

/-- Ambient stages are the bundled ideal-power submodules of `H^p(X, F)`. -/
theorem ambientStage_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    ambientStage I f F p n =
      Ideal.PowerSubmodule.stageObj I (Hom.cohomology f F p) n := sorry

/-- The inclusion of an ambient adic stage into `H^p(X, F)`. -/
noncomputable def ambientArrow (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    ambientStage I f F p n ⟶ Hom.cohomology f F p :=
  (Ideal.PowerSubmodule.subtypeNatTrans I n).app (Hom.cohomology f F p)

/-- The successor inclusion `I^(n+1) H^p(X, F) ⟶ I^n H^p(X, F)`. -/
noncomputable def ambientStep (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    ambientStage I f F p (n + 1) ⟶ ambientStage I f F p n :=
  Ideal.PowerSubmodule.inclusion I (Hom.cohomology f F p) (Nat.le_succ n)

/-- The inverse system `n ↦ I^n H^p(X, F)`, including the `n = 0` stage. -/
noncomputable def ambientTower (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) : SequentialInverseSystem (ModuleCat A) :=
  Functor.ofOpSequence (fun n ↦ ambientStep I f F p n)

/-- The object at index `n` of the ambient ideal-power tower. -/
theorem ambientTower_obj (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    (ambientTower I f F p).obj (op n) = ambientStage I f F p n := sorry

/-- Every successor transition of the ambient tower is `ambientStep`. -/
theorem ambientTower_stepMap (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p n : ℕ) :
    (ambientTower I f F p).stepMap n = ambientStep I f F p n := sorry

/-- The canonical inclusion `I^n H^p(X, F) ⟶ I^m H^p(X, F)` for `m ≤ n`. -/
noncomputable def ambientTransition (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    ambientStage I f F p n ⟶ ambientStage I f F p m :=
  Ideal.PowerSubmodule.inclusion I (Hom.cohomology f F p) h

/-- Every ambient-tower transition is the canonical adic inclusion. -/
theorem ambientTower_transitionMap (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p : ℕ) {m n : ℕ} (h : m ≤ n) :
    (ambientTower I f F p).transitionMap h = ambientTransition I f F p h := sorry

/-- Coefficient action of `a : I^(n-c)` on `H^p(X, I^c F)`. -/
noncomputable def mulMapApp (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p c n : ℕ) (h : c ≤ n) (a : (I ^ (n - c) : Ideal A)) :
    stage I f F p c ⟶ stage I f F p n :=
  (Hom.cohomologyFunctor f p).map
    (IdealPowerProduct.actionMap I f F (m := n - c) (n := c) a ≫
      eqToHom (congrArg (product I f F) (Nat.sub_add_cancel h)))

/-- Evaluating the coefficient action recovers cohomology of the sheaf-level action. -/
theorem mulMapApp_apply (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p c n : ℕ) (h : c ≤ n) (a : (I ^ (n - c) : Ideal A))
    (x : stage I f F p c) :
    mulMapApp I f F p c n h a x =
      ((Hom.cohomologyFunctor f p).map
        (IdealPowerProduct.actionMap I f F (m := n - c) (n := c) a ≫
          eqToHom (congrArg (product I f F) (Nat.sub_add_cancel h)))).hom x := sorry

/-- Tensor-lift of a family of maps out of a coefficient ideal, generic in the
`ModuleCat` source and target so the `A`-module structure is not unfolded. -/
noncomputable def tensorLiftIdeal (I : Ideal A) (k : ℕ) {M N : ModuleCat A}
    (action : (I ^ k : Ideal A) → (M ⟶ N)) :
    (tensorLeft (ModuleCat.of A (I ^ k : Ideal A))).obj M ⟶ N :=
  ModuleCat.ofHom
    (TensorProduct.lift
      { toFun := fun a => (action a).hom
        map_add' := sorry
        map_smul' := sorry })

/-- Tensor-lift is unchanged if the coefficient actions agree. -/
theorem tensorLiftIdeal_eq (I : Ideal A) (k : ℕ) {M N : ModuleCat A}
    {action action' : (I ^ k : Ideal A) → (M ⟶ N)}
    (h : action = action') :
    tensorLiftIdeal I k action = tensorLiftIdeal I k action' := sorry

/-- The Rees multiplication `I^(n-c) ⊗ H^p(X, I^c F) ⟶ H^p(X, I^n F)` for `n ≥ c`. -/
noncomputable def mulMap (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p c n : ℕ) (h : c ≤ n) :
    (tensorLeft (ModuleCat.of A (I ^ (n - c) : Ideal A))).obj (stage I f F p c) ⟶
      stage I f F p n :=
  tensorLiftIdeal I (n - c) (mulMapApp I f F p c n h)

/-- The Rees multiplication map is the tensor-lift of the coefficient actions. -/
theorem mulMap_eq (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p c n : ℕ) (h : c ≤ n) :
    mulMap I f F p c n h =
      tensorLiftIdeal I (n - c) (mulMapApp I f F p c n h) := sorry

/-- A shifted forward transformation is compatible with the maps to ambient cohomology. -/
def ForwardSpec (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p c : ℕ)
    (α : (tower I f F p).shift c ⟶ ambientTower I f F p) : Prop :=
  ∀ n : ℕ, α.app (op n) ≫ ambientArrow I f F p n = toAmbient I f F p (c + n)

/-- A shifted reverse transformation is canonical after mapping to ambient cohomology. -/
def ReverseSpec (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p c : ℕ)
    (β : (ambientTower I f F p).shift c ⟶ tower I f F p) : Prop :=
  ∀ n : ℕ, β.app (op n) ≫ toAmbient I f F p n = ambientArrow I f F p (c + n)

/-- Shifted comparison data between `H^p(X, I^n F)` and `I^n H^p(X, F)` for a single `c`. -/
structure Comparison (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.Modules) (p c : ℕ) where
  /-- The shifted maps from stage cohomology to ideal powers of ambient cohomology. -/
  forward : (tower I f F p).shift c ⟶ ambientTower I f F p
  /-- The shifted maps from ideal powers of ambient cohomology to stage cohomology. -/
  reverse : (ambientTower I f F p).shift c ⟶ tower I f F p
  /-- Compatibility of the forward maps with ambient cohomology. -/
  forward_spec : ForwardSpec I f F p c forward
  /-- Compatibility of the reverse maps with ambient cohomology. -/
  reverse_spec : ReverseSpec I f F p c reverse
  /-- The two transformations are inverse after the two fixed shifts. -/
  isShiftedInverse : Pro.SequentialHom.IsShiftedInverse c c forward reverse
  /-- Clause (1): Rees multiplication is surjective for every `n ≥ c`. -/
  mul_surjective :
    ∀ (n : ℕ) (hn : c ≤ n), Function.Surjective (mulMap I f F p c n hn).hom
  /-- Clause (2): images of tower transitions lie in the stated adic submodule. -/
  image_le :
    ∀ (n m : ℕ), c ≤ n + m →
      LinearMap.range (transition I f F p (Nat.le_add_right n m)).hom ≤
        Ideal.PowerSubmodule.stage I (stage I f F p n) (m - (c - n))
  /-- Clause (3): kernels of `toAmbient` and of the transition to stage `n-c` agree. -/
  ker_eq :
    ∀ (n : ℕ), c ≤ n →
      LinearMap.ker (toAmbient I f F p n).hom =
        LinearMap.ker (transition I f F p (Nat.sub_le n c)).hom

namespace Comparison

/-- Packages two shifted transformations and the five source clauses as comparison data. -/
def ofShiftedMaps {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ}
    (forward : (tower I f F p).shift c ⟶ ambientTower I f F p)
    (reverse : (ambientTower I f F p).shift c ⟶ tower I f F p)
    (forward_spec : ForwardSpec I f F p c forward)
    (reverse_spec : ReverseSpec I f F p c reverse)
    (isShiftedInverse : Pro.SequentialHom.IsShiftedInverse c c forward reverse)
    (mul_surjective :
      ∀ (n : ℕ) (hn : c ≤ n), Function.Surjective (mulMap I f F p c n hn).hom)
    (image_le :
      ∀ (n m : ℕ), c ≤ n + m →
        LinearMap.range (transition I f F p (Nat.le_add_right n m)).hom ≤
          Ideal.PowerSubmodule.stage I (stage I f F p n) (m - (c - n)))
    (ker_eq :
      ∀ (n : ℕ), c ≤ n →
        LinearMap.ker (toAmbient I f F p n).hom =
          LinearMap.ker (transition I f F p (Nat.sub_le n c)).hom) :
    Comparison I f F p c where
  forward := forward
  reverse := reverse
  forward_spec := forward_spec
  reverse_spec := reverse_spec
  isShiftedInverse := isShiftedInverse
  mul_surjective := mul_surjective
  image_le := image_le
  ker_eq := ker_eq

/-- All defining conditions of an affine-base cohomology comparison, exposed together. -/
theorem spec {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ} (D : Comparison I f F p c) :
    ForwardSpec I f F p c D.forward ∧ ReverseSpec I f F p c D.reverse ∧
      Pro.SequentialHom.IsShiftedInverse c c D.forward D.reverse ∧
      (∀ n (hn : c ≤ n), Function.Surjective (mulMap I f F p c n hn).hom) ∧
      (∀ n m, c ≤ n + m →
        LinearMap.range (transition I f F p (Nat.le_add_right n m)).hom ≤
          Ideal.PowerSubmodule.stage I (stage I f F p n) (m - (c - n))) ∧
      (∀ n, c ≤ n →
        LinearMap.ker (toAmbient I f F p n).hom =
          LinearMap.ker (transition I f F p (Nat.sub_le n c)).hom) := sorry

/-- Arithmetic bounds required for the two stable-range comparison composites. -/
theorem twoShiftBounds (c n : ℕ) (h : 2 * c ≤ n) :
    c ≤ n ∧ c ≤ n - c ∧ n - c - c ≤ n := sorry

/-- The factor `H^p(X, I^n F) ⟶ I^(n-c) H^p(X, F)` in the stable range. -/
noncomputable def forwardAt {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ} (D : Comparison I f F p c) (n : ℕ) (h : c ≤ n) :
    stage I f F p n ⟶ ambientStage I f F p (n - c) :=
  eqToHom (congrArg (stage I f F p) (Nat.add_sub_of_le h).symm) ≫
    D.forward.app (op (n - c))

/-- Composing the stable-range forward factor with the ambient inclusion recovers `toAmbient`. -/
theorem forwardAt_comp_toAmbient {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ} (D : Comparison I f F p c) (n : ℕ) (h : c ≤ n) :
    D.forwardAt n h ≫ ambientArrow I f F p (n - c) = toAmbient I f F p n := sorry

/-- The map `I^n H^p(X, F) ⟶ H^p(X, I^(n-c) F)` in the stable range. -/
noncomputable def reverseAt {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ} (D : Comparison I f F p c) (n : ℕ) (h : c ≤ n) :
    ambientStage I f F p n ⟶ stage I f F p (n - c) :=
  eqToHom (congrArg (ambientStage I f F p) (Nat.add_sub_of_le h).symm) ≫
    D.reverse.app (op (n - c))

/-- The stable-range reverse map has the canonical composite into ambient cohomology. -/
theorem reverseAt_comp_toAmbient {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ} (D : Comparison I f F p c) (n : ℕ) (h : c ≤ n) :
    D.reverseAt n h ≫ toAmbient I f F p (n - c) = ambientArrow I f F p n := sorry

/-- The reverse map followed by the forward factor is the canonical ambient-tower transition. -/
theorem reverse_forward {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ} (D : Comparison I f F p c) (n : ℕ) (h : 2 * c ≤ n) :
    D.reverseAt n (twoShiftBounds c n h).1 ≫
        D.forwardAt (n - c) (twoShiftBounds c n h).2.1 =
      ambientTransition I f F p (twoShiftBounds c n h).2.2 := sorry

/-- The forward factor followed by the reverse map is the canonical cohomology-tower
transition. -/
theorem forward_reverse {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ} (D : Comparison I f F p c) (n : ℕ) (h : 2 * c ≤ n) :
    D.forwardAt n (twoShiftBounds c n h).1 ≫
        D.reverseAt (n - c) (twoShiftBounds c n h).2.1 =
      transition I f F p (twoShiftBounds c n h).2.2 := sorry

/-- The explicit isomorphism of pro-objects determined by a cohomology comparison. -/
noncomputable abbrev toProIso {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ} (D : Comparison I f F p c) :=
  D.isShiftedInverse.iso

/-- `toProIso` is the shifted-inverse isomorphism of the two cohomology towers. -/
theorem toProIso_eq {I : Ideal A} {f : X ⟶ Spec (CommRingCat.of A)}
    {F : X.Modules} {p c : ℕ} (D : Comparison I f F p c) :
    D.toProIso = D.isShiftedInverse.iso := sorry

end Comparison

section ExistsComparison

variable [hA : IsNoetherianRing A]

include hA

/-- For a proper morphism to the spectrum of a Noetherian ring and a coherent sheaf, some `c`
witnesses all five ideal-power cohomology comparison clauses. -/
theorem existsComparison (I : Ideal A)
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ) :
    ∃ c : ℕ, Nonempty (Comparison I f F p c) := sorry

end ExistsComparison

end AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology
