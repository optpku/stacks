module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Diagram Transport of Homotopy-Colimit Presentations

This leaf transports a telescope presentation along an isomorphism of sequential diagrams.
The target coproduct cocone is supplied explicitly, so no `HasCoproduct` instance is needed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.DiagramIso

/-- The coproduct-to-cocone map after transporting a presentation to an isomorphic sequential
diagram with an explicitly supplied target coproduct cocone. -/
def toCocone {K L : ℕ ⥤ D} {X : D} (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) : Q.cocone.pt ⟶ X :=
  ColimitCocone.Discrete.map Q P.coproduct e.inv.app ≫ P.toCocone

/-- The connecting morphism after transporting a presentation to an isomorphic sequential
diagram with an explicitly supplied target coproduct cocone. -/
def connecting {K L : ℕ ⥤ D} {X : D} (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) : X ⟶ Q.cocone.pt⟦(1 : ℤ)⟧ :=
  P.connecting ≫ (ColimitCocone.Discrete.map P.coproduct Q e.hom.app)⟦(1 : ℤ)⟧'

/-- Transporting a presentation along a diagram isomorphism and an explicitly supplied target
coproduct cocone preserves distinguishedness of the telescope triangle. -/
@[stacks 090Z]
theorem distinguished {K L : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) :
    Triangle.mk (CoproductCocone.telescopeMap L Q)
      (toCocone P e Q) (connecting P e Q) ∈ distTriang D := sorry

end Presentation.DiagramIso

/-- Transport a telescope presentation along an isomorphism of sequential diagrams, using an
explicitly supplied coproduct cocone for the target diagram. -/
@[stacks 090Z]
def Presentation.ofDiagramIso {K L : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) : Presentation L X where
  coproduct := Q
  toCocone := DiagramIso.toCocone P e Q
  connecting := DiagramIso.connecting P e Q
  distinguished := DiagramIso.distinguished P e Q

/-- Diagram transport stores the explicitly supplied target coproduct cocone. -/
@[simp]
theorem Presentation.ofDiagramIso.coproduct {K L : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) :
    (P.ofDiagramIso e Q).coproduct = Q := sorry

/-- The coproduct-to-cocone map after diagram transport uses the reverse explicit coproduct
map. -/
@[simp]
theorem Presentation.ofDiagramIso.toCocone {K L : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) :
    (P.ofDiagramIso e Q).toCocone =
      ColimitCocone.Discrete.map Q P.coproduct e.inv.app ≫ P.toCocone := sorry

/-- The connecting map after diagram transport uses the forward shifted explicit coproduct
map. -/
@[simp]
theorem Presentation.ofDiagramIso.connecting {K L : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) :
    (P.ofDiagramIso e Q).connecting =
      P.connecting ≫ (ColimitCocone.Discrete.map P.coproduct Q e.hom.app)⟦(1 : ℤ)⟧' := sorry

/-- Every stage map after diagram transport is the original stage map precomposed with the
inverse component of the diagram isomorphism. -/
@[simp, reassoc]
theorem Presentation.ofDiagramIso.ι {K L : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) (n : ℕ) :
    (P.ofDiagramIso e Q).ι n = e.inv.app n ≫ P.ι n := sorry

/-- The cocone legs after diagram transport are precomposed with the inverse components of the
diagram isomorphism. -/
@[simp, reassoc]
theorem Presentation.ofDiagramIso.cocone_ι_app {K L : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) (n : ℕ) :
    (P.ofDiagramIso e Q).cocone.ι.app n =
      e.inv.app n ≫ P.cocone.ι.app n := sorry

/-- Transporting a presentation along the identity diagram isomorphism and retaining its
explicit coproduct cocone recovers the original presentation. -/
@[simp]
theorem Presentation.ofDiagramIso.refl {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) :
    P.ofDiagramIso (CategoryTheory.Iso.refl K) P.coproduct = P := sorry

/-- Successive diagram transports with explicit intermediate and target coproduct cocones
agree with transport along the composite diagram isomorphism. -/
@[simp]
theorem Presentation.ofDiagramIso.trans {K L M : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) (f : L ≅ M)
    (R : ColimitCocone (Discrete.functor M.obj)) :
    (P.ofDiagramIso e Q).ofDiagramIso f R =
      P.ofDiagramIso (e ≪≫ f) R := sorry

namespace Presentation.DiagramIso.Selected

/-- Transport a presentation along a diagram isomorphism using the coproduct cocone selected
by the target `HasCoproduct` instance. -/
@[stacks 090Z]
def transport {K L : ℕ ⥤ D} [HasCoproduct L.obj] {X : D}
    (P : Presentation K X) (e : K ≅ L) : Presentation L X :=
  P.ofDiagramIso e (getColimitCocone (Discrete.functor L.obj))

/-- Selected diagram transport stores the coproduct cocone selected by the target instance. -/
@[simp]
theorem transport.coproduct {K L : ℕ ⥤ D} [HasCoproduct L.obj] {X : D}
    (P : Presentation K X) (e : K ≅ L) :
    (transport P e).coproduct = getColimitCocone (Discrete.functor L.obj) := sorry

/-- The coproduct-to-cocone map of selected diagram transport is induced by the inverse
diagram map. -/
@[simp]
theorem transport.toCocone {K L : ℕ ⥤ D} [HasCoproduct L.obj] {X : D}
    (P : Presentation K X) (e : K ≅ L) :
    (transport P e).toCocone =
      ColimitCocone.Discrete.map (getColimitCocone (Discrete.functor L.obj))
        P.coproduct e.inv.app ≫ P.toCocone := sorry

/-- The connecting map of selected diagram transport is induced by the forward diagram map. -/
@[simp]
theorem transport.connecting {K L : ℕ ⥤ D} [HasCoproduct L.obj] {X : D}
    (P : Presentation K X) (e : K ≅ L) :
    (transport P e).connecting =
      P.connecting ≫
        (ColimitCocone.Discrete.map P.coproduct
          (getColimitCocone (Discrete.functor L.obj)) e.hom.app)⟦(1 : ℤ)⟧' := sorry

/-- Every stage map of selected diagram transport is the original stage map precomposed with
the inverse component of the diagram isomorphism. -/
@[simp, reassoc]
theorem transport.ι {K L : ℕ ⥤ D} [HasCoproduct L.obj] {X : D}
    (P : Presentation K X) (e : K ≅ L) (n : ℕ) :
    (transport P e).ι n = e.inv.app n ≫ P.ι n := sorry

/-- Successive selected diagram transports agree with selected transport along the composite
diagram isomorphism. -/
@[simp]
theorem transport.trans {K L M : ℕ ⥤ D}
    [HasCoproduct L.obj] [HasCoproduct M.obj] {X : D}
    (P : Presentation K X) (e : K ≅ L) (f : L ≅ M) :
    transport (transport P e) f = transport P (e ≪≫ f) := sorry

end Presentation.DiagramIso.Selected

namespace IsOf

namespace DiagramIso

/-- A homotopy-colimit predicate transports along a diagram isomorphism when a target
coproduct cocone is supplied explicitly. -/
@[stacks 0CRH]
theorem ofCoproduct {K L : ℕ ⥤ D} {X : D}
    (h : HomotopyColimit.IsOf K X) (e : K ≅ L)
    (Q : ColimitCocone (Discrete.functor L.obj)) :
    HomotopyColimit.IsOf L X := sorry

end DiagramIso

/-- The homotopy-colimit predicate is stable under an isomorphism of sequential diagrams. -/
@[stacks 0CRH]
theorem ofDiagramIso {K L : ℕ ⥤ D} {X : D}
    (h : HomotopyColimit.IsOf K X) (e : K ≅ L) :
    HomotopyColimit.IsOf L X := sorry

end IsOf

end CategoryTheory.HomotopyColimit
