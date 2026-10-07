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
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.QuasiSeparated

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
instance hom_isSeparated : IsSeparated hom := sorry

/-- The infinite coproduct fold is not quasi-compact. -/
theorem not_quasiCompact_hom : ¬ QuasiCompact hom := sorry

/-- Lemma 110.30.1 (1): the pushforward of the structure sheaf along `hom` is not
quasi-coherent. This morphism is separated and not quasi-compact, so quasi-compactness
cannot be omitted from Schemes, Lemma 26.24.1. -/
@[stacks 078D]
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
instance hom_quasiCompact : QuasiCompact (hom k) := sorry

/-- The doubled-scheme fold is not quasi-separated. -/
theorem not_quasiSeparated_hom : ¬ QuasiSeparated (hom k) := sorry

/-- Lemma 110.30.1 (2): the pushforward of the structure sheaf along `hom` is not
quasi-coherent. For a field `k` this morphism is quasi-compact and not quasi-separated,
so quasi-separatedness cannot be omitted from Schemes, Lemma 26.24.1. -/
@[stacks 078D]
theorem not_isQuasicoherent :
    ¬ ((Scheme.Modules.pushforward (hom k)).obj
        (SheafOfModules.unit (scheme k).ringCatSheaf)).IsQuasicoherent := sorry

end GluedCopies

end pushforward

end AlgebraicGeometry.Scheme.Modules
