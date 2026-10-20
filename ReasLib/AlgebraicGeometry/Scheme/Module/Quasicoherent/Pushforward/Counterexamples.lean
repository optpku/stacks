module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Counterexamples for quasi-coherent pushforwards
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open MvPolynomial
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

namespace pushforward

namespace InfiniteCoproduct

/-- The infinite disjoint union of copies of `Spec ℤ`, indexed by `ℕ`. -/
def scheme : Scheme.{u} :=
  ∐ fun _ : ULift.{u} ℕ ↦ Spec (.of (ULift.{u} ℤ))

/-- The fold morphism from the infinite coproduct of copies of `Spec ℤ` onto `Spec ℤ`. -/
def hom : scheme ⟶ Spec (.of (ULift.{u} ℤ)) :=
  Sigma.desc fun _ ↦ 𝟙 (Spec (.of (ULift.{u} ℤ)))

/-- The infinite coproduct fold is a separated morphism. -/
@[instance]
theorem hom_isSeparated : IsSeparated hom := sorry

/-- The infinite coproduct fold is not quasi-compact. -/
theorem not_quasiCompact_hom : ¬ QuasiCompact hom := sorry

/-- The pushforward of the structure sheaf along the infinite coproduct fold is not
quasi-coherent. -/
theorem not_isQuasicoherent :
    ¬ ((Scheme.Modules.pushforward hom).obj
        (SheafOfModules.unit scheme.ringCatSheaf)).IsQuasicoherent := sorry

end InfiniteCoproduct

namespace GluedCopies

/-- The polynomial variables `t`, `z`, and `x n` for `n : ℕ` standing for `x_{n+1}`. -/
inductive Vars
  | t
  | z
  | x : ℕ → Vars
  deriving DecidableEq

variable (k : Type u) [Field k]

/-- The ideal of relations `(t ^ (n + 1) * x n ^ (n + 1) * z)` in `k[t, z, x n]`. -/
def relIdeal : Ideal (MvPolynomial Vars k) :=
  Ideal.span (Set.range fun n : ℕ ↦ X (.t) ^ (n + 1) * X (.x n) ^ (n + 1) * X (.z))

/-- The coordinate ring
`A = k[t, z, x n] ⧸ (t ^ (n + 1) * x n ^ (n + 1) * z)`. -/
abbrev ring : Type u := MvPolynomial Vars k ⧸ relIdeal k

/-- The affine scheme `Y = Spec A`. -/
def affine : Scheme.{u} := Spec (CommRingCat.of (ring k))

/-- The global section of `affine` corresponding to the image of `x n` in `ring`. -/
def xSection (n : ℕ) : Γ(affine k, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (ring k))).inv
    (Ideal.Quotient.mk (relIdeal k) (X (.x n)))

/-- The open subscheme `V = ⋃ D(x n)` of `affine`. -/
def overlap : (affine k).Opens :=
  ⨆ n : ℕ, (affine k).basicOpen (xSection k n)

/-- The scheme obtained by gluing two copies of `affine` along `overlap`. -/
def scheme : Scheme.{u} := doubleAlong (overlap k)

/-- The fold morphism from the doubled scheme onto `affine`. -/
def hom : scheme k ⟶ affine k := DoubleAlong.fold (overlap k)

/-- The open immersion of `overlap` into `affine` is not quasi-compact. -/
theorem not_quasiCompact_overlap_ι : ¬ QuasiCompact (overlap k).ι := sorry

/-- The doubled-scheme fold is a quasi-compact morphism. -/
@[instance]
theorem hom_quasiCompact : QuasiCompact (hom k) := sorry

/-- The pushforward of the structure sheaf along the doubled-scheme fold is not
quasi-coherent. -/
theorem not_isQuasicoherent :
    ¬ ((Scheme.Modules.pushforward (hom k)).obj
        (SheafOfModules.unit (scheme k).ringCatSheaf)).IsQuasicoherent := sorry

end GluedCopies

/-- The quasi-compactness and quasi-separatedness hypotheses for preserving
quasi-coherence under pushforward are both necessary. -/
@[stacks 078D]
theorem qcqs_hypotheses_are_necessary (k : Type u) [Field k] :
    (IsSeparated InfiniteCoproduct.hom ∧
      ¬ QuasiCompact InfiniteCoproduct.hom ∧
      (SheafOfModules.unit InfiniteCoproduct.scheme.ringCatSheaf).IsQuasicoherent ∧
      ¬ ((Scheme.Modules.pushforward InfiniteCoproduct.hom).obj
        (SheafOfModules.unit InfiniteCoproduct.scheme.ringCatSheaf)).IsQuasicoherent) ∧
    (QuasiCompact (GluedCopies.hom k) ∧
      ¬ QuasiSeparated (GluedCopies.hom k) ∧
      (SheafOfModules.unit (GluedCopies.scheme k).ringCatSheaf).IsQuasicoherent ∧
      ¬ ((Scheme.Modules.pushforward (GluedCopies.hom k)).obj
        (SheafOfModules.unit (GluedCopies.scheme k).ringCatSheaf)).IsQuasicoherent) := by
  constructor
  · exact ⟨InfiniteCoproduct.hom_isSeparated,
      InfiniteCoproduct.not_quasiCompact_hom,
      inferInstance,
      InfiniteCoproduct.not_isQuasicoherent⟩
  · refine ⟨GluedCopies.hom_quasiCompact k, ?_, inferInstance,
      GluedCopies.not_isQuasicoherent k⟩
    exact Scheme.DoubleAlong.fold_not_quasiSeparated (GluedCopies.overlap k)
      (GluedCopies.not_quasiCompact_overlap_ι k)

end pushforward

end AlgebraicGeometry.Scheme.Modules
