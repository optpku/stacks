module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.StandardOpenCover

/-!
# Finite standard Zariski covers of schemes

This module gives the scheme-facing views of the ring-level owner
`PrimeSpectrum.StandardOpenCoverOf`. It refines Mathlib's general
`Scheme.OpenCover` without imposing an irrelevant enumeration by `Fin n`.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry
namespace Scheme

variable (T : Scheme.{u})

/-- A standard Zariski cover of `T` is a finite principal-open cover associated
to global sections of `T`, with an arbitrary finite index type. -/
@[stacks 020R]
abbrev StandardZariskiCover : Type (max u (v + 1)) :=
  PrimeSpectrum.StandardOpenCoverOf.{u, v} (1 : Γ(T, ⊤))

namespace StandardZariskiCover

variable {T : Scheme.{u}}

/-- The finite index type of a standard Zariski cover. -/
@[stacks 020R "standard Zariski cover index"]
abbrev index (𝒰 : T.StandardZariskiCover.{u, v}) : Type v :=
  PrimeSpectrum.StandardOpenCoverOf.index 𝒰

/-- The family of distinguished opens underlying a standard Zariski cover. -/
@[stacks 020R "standard Zariski cover family"]
def opens (𝒰 : T.StandardZariskiCover.{u, v}) : 𝒰.index → T.Opens :=
  fun i ↦ T.basicOpen (𝒰.generator i)

/-- Evaluation of the distinguished-open family underlying a standard Zariski cover. -/
@[simp, stacks 020R "standard Zariski cover family evaluation"]
theorem opens_apply (𝒰 : T.StandardZariskiCover.{u, v}) (i : 𝒰.index) :
    𝒰.opens i = T.basicOpen (𝒰.generator i) := sorry

/-- The `i`-th distinguished open in a standard Zariski cover, viewed as an open subscheme of
`T`. -/
@[stacks 020R "standard Zariski cover member scheme"]
abbrev X (𝒰 : T.StandardZariskiCover.{u, v}) (i : 𝒰.index) : Scheme.{u} :=
  T.basicOpen (𝒰.generator i)

/-- The inclusion of the `i`-th distinguished open into `T`. -/
@[stacks 020R "standard Zariski cover member inclusion"]
abbrev f (𝒰 : T.StandardZariskiCover.{u, v}) (i : 𝒰.index) : 𝒰.X i ⟶ T :=
  (T.basicOpen (𝒰.generator i)).ι

/-- The top open of `T` is the supremum of the chosen distinguished opens. -/
@[stacks 020R "standard Zariski cover equality"]
theorem basicOpen_eq_iSup (𝒰 : T.StandardZariskiCover.{u, v}) :
    (⊤ : T.Opens) = ⨆ i : 𝒰.index, 𝒰.opens i := sorry

/-- The distinguished-open family of a standard Zariski cover has supremum `⊤`. -/
@[stacks 020R "standard Zariski cover supremum"]
theorem iSup_eq_top (𝒰 : T.StandardZariskiCover.{u, v}) :
    (⨆ i : 𝒰.index, 𝒰.opens i) = (⊤ : T.Opens) := sorry

/-- The distinguished-open family underlying a standard Zariski cover is an open cover. -/
@[stacks 020R "standard Zariski open cover"]
theorem isOpenCover (𝒰 : T.StandardZariskiCover.{u, v}) :
    TopologicalSpace.IsOpenCover 𝒰.opens := sorry

/-- The underlying distinguished-open family, viewed as an ordinary open cover of `T`. -/
@[stacks 020R "standard Zariski cover as a scheme open cover"]
abbrev toOpenCover (𝒰 : T.StandardZariskiCover.{u, v}) : T.OpenCover :=
  Scheme.openCoverOfIsOpenCover T 𝒰.opens 𝒰.isOpenCover

/-- The objects of `toOpenCover` are the chosen distinguished opens. -/
@[simp, stacks 020R "standard Zariski cover object readout"]
theorem toOpenCover_X (𝒰 : T.StandardZariskiCover.{u, v}) (i : 𝒰.index) :
    𝒰.toOpenCover.X i = 𝒰.X i := sorry

/-- The maps of `toOpenCover` are the inclusions of the chosen distinguished opens. -/
@[simp, stacks 020R "standard Zariski cover map readout"]
theorem toOpenCover_f (𝒰 : T.StandardZariskiCover.{u, v}) (i : 𝒰.index) :
    𝒰.toOpenCover.f i = 𝒰.f i := sorry

/-- The range of the `i`-th component is the distinguished open cut out by `𝒰.generator i`. -/
@[stacks 020R "standard Zariski cover range"]
theorem opensRange_eq_basicOpen (𝒰 : T.StandardZariskiCover.{u, v}) (i : 𝒰.index) :
    (𝒰.f i).opensRange = T.basicOpen (𝒰.generator i) := sorry

/-- Every component of a standard Zariski cover of an affine scheme is affine. -/
@[stacks 020R "standard Zariski cover affine member"]
theorem isAffine_obj [IsAffine T] (𝒰 : T.StandardZariskiCover.{u, v}) (i : 𝒰.index) :
    IsAffine (𝒰.X i) := sorry

end StandardZariskiCover

end Scheme
end AlgebraicGeometry
