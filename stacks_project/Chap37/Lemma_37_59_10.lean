/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Triangulated
import StacksCheckRecall

open CategoryTheory CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme.ModuleDerived
open scoped AlgebraicGeometry

universe u

/- Lemma 37.59.10 (1): in a distinguished triangle, relative `(m + 1)`-pseudo-coherence
of the first vertex and relative `m`-pseudo-coherence of the second imply relative
`m`-pseudo-coherence of the third. -/
@[stacks 09UL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.obj₃ :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (m : ℤ)
      (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
      (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
      (h₁ : IsMPseudoCoherentOver f T.obj₁ (m + 1))
      (h₂ : IsMPseudoCoherentOver f T.obj₂ m),
      IsMPseudoCoherentOver f T.obj₃ m)

/- Lemma 37.59.10 (2): in a distinguished triangle, relative `m`-pseudo-coherence of the
first and third vertices implies relative `m`-pseudo-coherence of the second. -/
@[stacks 09UL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.obj₂ :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (m : ℤ)
      (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
      (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
      (h₁ : IsMPseudoCoherentOver f T.obj₁ m)
      (h₃ : IsMPseudoCoherentOver f T.obj₃ m),
      IsMPseudoCoherentOver f T.obj₂ m)

/- Lemma 37.59.10 (3): in a distinguished triangle, relative `(m + 1)`-pseudo-coherence
of the second vertex and relative `m`-pseudo-coherence of the third imply relative
`(m + 1)`-pseudo-coherence of the first. -/
@[stacks 09UL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.obj₁ :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (m : ℤ)
      (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
      (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
      (h₂ : IsMPseudoCoherentOver f T.obj₂ (m + 1))
      (h₃ : IsMPseudoCoherentOver f T.obj₃ m),
      IsMPseudoCoherentOver f T.obj₁ (m + 1))

/- Lemma 37.59.10 (4): in a distinguished triangle, relative pseudo-coherence of the
first two vertices implies relative pseudo-coherence of the third. -/
@[stacks 09UL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsPseudoCoherentOver.obj₃ :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
      (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
      (h₁ : IsPseudoCoherentOver f T.obj₁)
      (h₂ : IsPseudoCoherentOver f T.obj₂),
      IsPseudoCoherentOver f T.obj₃)

/- Lemma 37.59.10 (5): in a distinguished triangle, relative pseudo-coherence of the
first and third vertices implies relative pseudo-coherence of the second. -/
@[stacks 09UL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsPseudoCoherentOver.obj₂ :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
      (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
      (h₁ : IsPseudoCoherentOver f T.obj₁)
      (h₃ : IsPseudoCoherentOver f T.obj₃),
      IsPseudoCoherentOver f T.obj₂)

/- Lemma 37.59.10 (6): in a distinguished triangle, relative pseudo-coherence of the
second and third vertices implies relative pseudo-coherence of the first. -/
@[stacks 09UL] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsPseudoCoherentOver.obj₁ :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
      (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
      (h₂ : IsPseudoCoherentOver f T.obj₂)
      (h₃ : IsPseudoCoherentOver f T.obj₃),
      IsPseudoCoherentOver f T.obj₁)
