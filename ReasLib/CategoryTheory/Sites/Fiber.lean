module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Fiber of a sheaf morphism over a section

Given a morphism `π : E ⟶ B` of sheaves on a site `(C, J)` and a section
`b ∈ B(U)`, the fiber `π⁻¹(b)` is naturally a sheaf on the slice site `C/U`.
This is the sheaf-theoretic analogue of the fiber of a map of sets.

## Main definitions

- `sectionFiberSubfunctor` — the subfunctor of `E` restricting to fibers over `b`
- `sectionFiberPresheaf` — the presheaf of fibers (on the slice)
- `sectionFiberSheaf` — the sheaf of fibers (on the slice)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

section

variable {E B : Sheaf J (Type w)} {U : C}

/-- Restriction preserves the fiber condition: if `s` maps to `b` over `X`, then
its restriction along any slice morphism maps to `b` restricted correspondingly. -/
theorem sectionFiber_map_mem
    (π : E ⟶ B) (b : B.obj.obj (op U))
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y)
    {s : E.obj.obj (op X.unop.left)}
    (hs : π.hom.app (op X.unop.left) s = B.obj.map X.unop.hom.op b) :
    π.hom.app (op Y.unop.left) (E.obj.map f.unop.left.op s) =
      B.obj.map Y.unop.hom.op b := sorry

/-- The subfunctor of `E` over the slice `C/U` consisting of sections mapping to `b`. -/
def sectionFiberSubfunctor
    (π : E ⟶ B) (b : B.obj.obj (op U)) : (Over U)ᵒᵖ ⥤ Type w where
  obj X := { s : E.obj.obj (op X.unop.left) // π.hom.app _ s = B.obj.map X.unop.hom.op b }
  map {X Y} f := ↾fun s =>
    ⟨E.obj.map f.unop.left.op s.val, sectionFiber_map_mem π b f s.property⟩
  map_id := sorry
  map_comp := sorry

/-- The presheaf of fibers over `b`, as a presheaf on the slice. -/
abbrev sectionFiberPresheaf
    (π : E ⟶ B) (b : B.obj.obj (op U)) : (Over U)ᵒᵖ ⥤ Type w :=
  sectionFiberSubfunctor π b

/-- The fiber presheaf is a sheaf for the slice topology. -/
theorem sectionFiberPresheaf_isSheaf
    (π : E ⟶ B) (b : B.obj.obj (op U)) :
    Presheaf.IsSheaf (J.over U) (sectionFiberPresheaf π b) := sorry

/-- The type-valued fiber presheaf satisfies the equivalent presieve sheaf condition. -/
theorem sectionFiberPresheaf_isSheaf_of_types
    (π : E ⟶ B) (b : B.obj.obj (op U)) :
    Presieve.IsSheaf (J.over U) (sectionFiberPresheaf π b) := sorry

/-- The fiber of `π` over `b`, as a sheaf on the slice site `(C/U, J.over U)`. -/
abbrev sectionFiberSheaf
    (π : E ⟶ B) (b : B.obj.obj (op U)) : Sheaf (J.over U) (Type w) :=
  ⟨sectionFiberPresheaf π b, sectionFiberPresheaf_isSheaf π b⟩

end

end CategoryTheory
