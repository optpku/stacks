/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Triangulated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Restriction

@[expose] public section

/-!
# Distinguished triangles of relatively pseudo-coherent derived modules

Relative pseudo-coherence of derived modules over a locally finite type morphism of schemes is
stable under the three vertices of a distinguished triangle.
-/

open CategoryTheory CategoryTheory.Pretriangulated
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X S : Scheme.{u}}

namespace IsMPseudoCoherentOver

/-- The third vertex of a distinguished triangle inherits relative `m`-pseudo-coherence
from relative `(m + 1)`-pseudo-coherence of the first vertex and relative
`m`-pseudo-coherence of the second. -/
theorem obj₃ (f : X ⟶ S) [LocallyOfFiniteType f] (m : ℤ)
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : IsMPseudoCoherentOver f T.obj₁ (m + 1))
    (h₂ : IsMPseudoCoherentOver f T.obj₂ m) :
    IsMPseudoCoherentOver f T.obj₃ m := sorry

/-- The middle vertex of a distinguished triangle inherits relative `m`-pseudo-coherence
from the first and third vertices. -/
theorem obj₂ (f : X ⟶ S) [LocallyOfFiniteType f] (m : ℤ)
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : IsMPseudoCoherentOver f T.obj₁ m)
    (h₃ : IsMPseudoCoherentOver f T.obj₃ m) :
    IsMPseudoCoherentOver f T.obj₂ m := sorry

/-- The first vertex of a distinguished triangle inherits relative `(m + 1)`-pseudo-coherence
from relative `(m + 1)`-pseudo-coherence of the second vertex and relative
`m`-pseudo-coherence of the third. -/
theorem obj₁ (f : X ⟶ S) [LocallyOfFiniteType f] (m : ℤ)
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₂ : IsMPseudoCoherentOver f T.obj₂ (m + 1))
    (h₃ : IsMPseudoCoherentOver f T.obj₃ m) :
    IsMPseudoCoherentOver f T.obj₁ (m + 1) := sorry

end IsMPseudoCoherentOver

namespace IsPseudoCoherentOver

/-- The third vertex of a distinguished triangle is relatively pseudo-coherent when its
first two vertices are. -/
theorem obj₃ (f : X ⟶ S) [LocallyOfFiniteType f]
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : IsPseudoCoherentOver f T.obj₁)
    (h₂ : IsPseudoCoherentOver f T.obj₂) :
    IsPseudoCoherentOver f T.obj₃ := sorry

/-- The middle vertex of a distinguished triangle is relatively pseudo-coherent when its
first and third vertices are. -/
theorem obj₂ (f : X ⟶ S) [LocallyOfFiniteType f]
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : IsPseudoCoherentOver f T.obj₁)
    (h₃ : IsPseudoCoherentOver f T.obj₃) :
    IsPseudoCoherentOver f T.obj₂ := sorry

/-- The first vertex of a distinguished triangle is relatively pseudo-coherent when its
second and third vertices are. -/
theorem obj₁ (f : X ⟶ S) [LocallyOfFiniteType f]
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₂ : IsPseudoCoherentOver f T.obj₂)
    (h₃ : IsPseudoCoherentOver f T.obj₃) :
    IsPseudoCoherentOver f T.obj₁ := sorry

end IsPseudoCoherentOver

end AlgebraicGeometry.Scheme.ModuleDerived
