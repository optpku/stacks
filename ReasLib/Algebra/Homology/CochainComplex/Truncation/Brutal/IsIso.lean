module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Trunc
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Map
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Stupid.Functor.IsIso
public import ReasLib.CategoryTheory.Filtration.Complex.NegStage.IsIso

/-!
# Isomorphism transport for brutal truncation towers

This leaf provides componentwise and bundled `IsIso` instances for both the
filtration-stage tower and its `stupidTrunc` presentation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Stage

variable {K L : CochainComplex A ℤ}

/-- Every degree component of a brutal-stage map is an isomorphism when the cochain map is. -/
@[stacks 0D8Z]
noncomputable instance map_f_isIso (f : K ⟶ L) (p i : ℤ) [IsIso f] :
    IsIso ((map f p).f i) := sorry

/-- A fixed brutal-stage map is an isomorphism when the cochain map is. -/
@[stacks 0D8Z]
noncomputable instance map_isIso (f : K ⟶ L) (p : ℤ) [IsIso f] :
    IsIso (map f p) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso ((map f 0).f 0)
#synth IsIso (map f 0)

end Stage

namespace Tower

variable {K L : CochainComplex A ℤ}

/-- Every component of a filtration-stage brutal tower map is an isomorphism
when the cochain map is. -/
@[stacks 0D8Z]
noncomputable instance map_app_isIso (f : K ⟶ L) (n : ℕ) [IsIso f] :
    IsIso ((map f).app n) := sorry

/-- A direct component map of a filtration-stage brutal tower is an isomorphism
when the cochain map is. -/
@[stacks 0D8Z]
noncomputable instance mapApp_isIso (f : K ⟶ L) (n : ℕ) [IsIso f] :
    IsIso (mapApp f n) := sorry

/-- A filtration-stage brutal tower map is an isomorphism when the cochain map is. -/
@[stacks 0D8Z]
noncomputable instance map_isIso (f : K ⟶ L) [IsIso f] :
    IsIso (map f) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso ((map f).app 0)
#synth IsIso (mapApp f 0)
#synth IsIso (map f)

end Tower

namespace Trunc

variable {K L : CochainComplex A ℤ}

/-- Every component of a `stupidTrunc` brutal tower map is an isomorphism
when the cochain map is. -/
@[stacks 0D8Z]
noncomputable instance map_app_isIso (f : K ⟶ L) (n : ℕ) [IsIso f] :
    IsIso ((map f).app n) := sorry

/-- A direct `stupidTrunc` component map is an isomorphism when the cochain map is. -/
@[stacks 0D8Z]
noncomputable instance mapApp_isIso (f : K ⟶ L) (n : ℕ) [IsIso f] :
    IsIso (mapApp f n) := sorry

/-- A `stupidTrunc` brutal tower map is an isomorphism when the cochain map is. -/
@[stacks 0D8Z]
noncomputable instance map_isIso (f : K ⟶ L) [IsIso f] :
    IsIso (map f) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso ((map f).app 0)
#synth IsIso (mapApp f 0)
#synth IsIso (map f)

end Trunc

end CategoryTheory.CochainComplex.Brutal
