module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc

/-!
# Fpqc descent of relatively ample modules

Relative ampleness of invertible scheme modules is local for fpqc covering families.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.RelativelyAmple

/-- An invertible module is relatively ample if and only if each of its canonical base
changes along an fpqc covering family is relatively ample. -/
theorem iff_forall_baseChange_of_fpqcCovering
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [L.Invertible]
    {ι : Type v} (family : ι → Over S) (hfamily : Scheme.FpqcCovering family) :
    RelativelyAmple f L ↔
      ∀ i : ι, RelativelyAmple (pullback.snd f (family i).hom)
        (Scheme.Modules.baseChangeModule f (family i).hom L) := sorry

end AlgebraicGeometry.RelativelyAmple
