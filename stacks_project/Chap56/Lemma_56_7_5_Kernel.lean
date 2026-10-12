/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))

/-- A coherent kernel on `Limits.pullback x y` for the Coh-level Fourier--Mukai
comparison is coherent, flat over `X`, and has scheme-theoretic support finite
over `Y`. -/
class IsCoherentFourierMukaiKernel (K : (Limits.pullback x y).Modules) : Prop where
  isCoherent : K.IsCoherent
  flatOver : Scheme.Modules.flatOver K (Limits.pullback.fst x y)
  supportFinite :
    IsFinite
      ((Scheme.Modules.schemeTheoreticSupport K).subschemeι ≫ Limits.pullback.snd x y)

/-- Coherent Fourier--Mukai kernels are characterized by coherence, flatness over
`X`, and finiteness of scheme-theoretic support over `Y`. -/
theorem isCoherentFourierMukaiKernel_iff (K : (Limits.pullback x y).Modules) :
    IsCoherentFourierMukaiKernel x y K ↔
      K.IsCoherent ∧
        Scheme.Modules.flatOver K (Limits.pullback.fst x y) ∧
          IsFinite
            ((Scheme.Modules.schemeTheoreticSupport K).subschemeι ≫
              Limits.pullback.snd x y) := sorry

/-- Coherent Fourier--Mukai kernels are coherent modules. -/
instance instIsCoherent_isCoherentFourierMukaiKernel
    (K : (Limits.pullback x y).Modules) [h : IsCoherentFourierMukaiKernel x y K] :
    K.IsCoherent :=
  h.isCoherent

/-- Coherent Fourier--Mukai kernels are quasicoherent. -/
instance instIsQuasicoherent_isCoherentFourierMukaiKernel
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K] :
    K.IsQuasicoherent := sorry

/-- Coherent Fourier--Mukai kernels are flat over `X`. -/
theorem flatOver_of_isCoherentFourierMukaiKernel
    (K : (Limits.pullback x y).Modules) [h : IsCoherentFourierMukaiKernel x y K] :
    Scheme.Modules.flatOver K (Limits.pullback.fst x y) :=
  h.flatOver

/-- The scheme-theoretic support of a coherent Fourier--Mukai kernel is finite over
`Y`. -/
instance instIsFinite_support_isCoherentFourierMukaiKernel
    (K : (Limits.pullback x y).Modules) [h : IsCoherentFourierMukaiKernel x y K] :
    IsFinite
      ((Scheme.Modules.schemeTheoreticSupport K).subschemeι ≫ Limits.pullback.snd x y) :=
  h.supportFinite

/-- The quasicoherent module associated to a coherent Fourier--Mukai kernel. -/
def IsCoherentFourierMukaiKernel.toQCoh (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] : Scheme.QCoh (Limits.pullback x y) :=
  ⟨K, inferInstance⟩

/-- The underlying module of `IsCoherentFourierMukaiKernel.toQCoh` is the given
kernel. -/
theorem IsCoherentFourierMukaiKernel.toQCoh_obj (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    (IsCoherentFourierMukaiKernel.toQCoh x y K).obj = K := sorry

/-- The full subcategory of coherent kernels on `Limits.pullback x y` that are
flat over `X` with support finite over `Y`. -/
abbrev coherentFourierMukaiKernel :=
  ObjectProperty.FullSubcategory fun K : (Limits.pullback x y).Modules ↦
    IsCoherentFourierMukaiKernel x y K

/-- Objects of `coherentFourierMukaiKernel` are coherent Fourier--Mukai kernels. -/
instance instIsCoherentFourierMukaiKernel_coherentFourierMukaiKernel
    (K : coherentFourierMukaiKernel x y) :
    IsCoherentFourierMukaiKernel x y K.obj :=
  K.property

/-- Objects of `coherentFourierMukaiKernel` satisfy the kernel property. -/
theorem coherentFourierMukaiKernel_property (K : coherentFourierMukaiKernel x y) :
    IsCoherentFourierMukaiKernel x y K.obj :=
  inferInstance

end AlgebraicGeometry.Scheme
