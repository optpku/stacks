/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FormalCompletion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

variable (A : SequentialInverseSystem CommRingCat.{u})
variable (A_lim : LimitCone A)
variable (h_surjective : A.Surjective)
variable (h_kernel : A.KernelLocallyNilpotent)

variable (X : Scheme.{u}) (f : X ⟶ Spec A_lim.cone.pt)
variable [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]

variable (Xn : ℕ → Scheme.{u})
variable (p : ∀ n, Xn n ⟶ X)
variable (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n)))
variable (h_pullback : ∀ n,
  IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
variable (h_closed : ∀ n, IsClosedImmersion (p n))

variable (i : ∀ n, Xn n ⟶ Xn (n + 1))
variable (hiX : ∀ n, i n ≫ p (n + 1) = p n)
variable (hiA : ∀ n,
  i n ≫ q (n + 1) = q n ≫ Spec.map (A.stepMap n))

variable (K : ∀ n, RingedSpace.ModuleDerived (Xn n).toRingedSpace)
variable (hK : ∀ n, RingedSpace.ModuleDerived.IsPseudoCoherent (K n))
variable [∀ n, HasPair (RingedSpace.opensRingedSiteHom (i n).toShHom)]
variable (φ : ∀ n, K (n + 1) ⟶
  (RingedSpace.moduleDerivedPushforward (i n).toShHom).obj (K n))
variable (hφ : ∀ n, IsIso
  (((RingedSpace.modulePullbackDerivedPushforwardAdjunction (i n).toShHom).homEquiv
    (K (n + 1)) (K n)).symm (φ n)))

/- Situation 38.29.1: `A_lim` realizes `A = lim Aₙ`, the transition maps of `A`
are surjective with locally nilpotent kernels, and `f : X ⟶ Spec A` is proper,
flat, and of finite presentation. Each square defining `Xn n` is cartesian and
`p n : Xn n ⟶ X` is a closed immersion. The pseudo-coherent objects `K n` are
linked by `φ n : K (n + 1) ⟶ R(i n)_* K n`; its adjoint derived pullback map is
an isomorphism. -/
@[stacks 0DIB] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion.System.of
    (A := A) (A_lim := A_lim) (X := X) (f := f)
    (Xn := Xn) (p := p) (q := q) (i := i)
    h_surjective h_kernel h_pullback h_closed hiX hiA K hK φ hφ :
    AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion.System
      A A_lim X f Xn p q i)
