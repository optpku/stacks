/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Iso.Operations
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Presentation.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms induced by presentation isomorphisms

A compatible isomorphism of telescope presentations induces an isomorphism of represented Hom
Milnor short complexes and a natural isomorphism in the represented target.
@stack 0CQX
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.RepresentedHom

open SequentialInverseSystem.Milnor.ProductCone

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The left-component square used to construct the short-complex isomorphism associated to
a compatible presentation isomorphism. -/
theorem shortComplexIso_comm₁₂ {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) (Z : D) :
    (canonicalR1.mapIso (shiftedTowerPrecompIso e Z)).hom ≫ r1Inclusion P Z =
      r1Inclusion Q Z ≫ ((preadditiveYoneda.obj Z).mapIso Φ.iso.op).hom := sorry

/-- The right-component square used to construct the short-complex isomorphism associated to
a compatible presentation isomorphism. -/
theorem shortComplexIso_comm₂₃ {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) (Z : D) :
    ((preadditiveYoneda.obj Z).mapIso Φ.iso.op).hom ≫ homToLimit P Z =
      homToLimit Q Z ≫ (Limits.lim.mapIso (towerPrecompIso e Z)).hom := sorry

/-- A compatible isomorphism of telescope presentations induces a contravariant isomorphism
of represented Hom Milnor short complexes. -/
@[stacks 0CQX]
def shortComplexIso {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) (Z : D) :
    shortComplex Q Z ≅ shortComplex P Z :=
  ShortComplex.isoMk
    (canonicalR1.mapIso (shiftedTowerPrecompIso e Z))
    ((preadditiveYoneda.obj Z).mapIso Φ.iso.op)
    (Limits.lim.mapIso (towerPrecompIso e Z))
    (shortComplexIso_comm₁₂ Φ Z) (shortComplexIso_comm₂₃ Φ Z)

/-- The forward morphism of `shortComplexIso` is the short-complex precomposition map attached
to the forward presentation morphism. -/
@[simp]
theorem shortComplexIso_hom {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) (Z : D) :
    (shortComplexIso Φ Z).hom = shortComplexPrecomp Φ.toHom Z := sorry

/-- The inverse morphism of `shortComplexIso` is the short-complex precomposition map attached
to the inverse presentation isomorphism. -/
@[simp]
theorem shortComplexIso_inv {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) (Z : D) :
    (shortComplexIso Φ Z).inv = shortComplexPrecomp Φ.symm.toHom Z := sorry

/-- The short-complex isomorphism induced by a presentation isomorphism is natural in the
represented target. -/
@[reassoc, stacks 0CQX]
theorem shortComplexIso_naturality
    {K L : ℕ ⥤ D} {e : K ≅ L} {X Y Z W : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) (f : Z ⟶ W) :
    shortComplexMap Q f ≫ (shortComplexIso Φ W).hom =
      (shortComplexIso Φ Z).hom ≫ shortComplexMap P f := sorry

/-- A compatible presentation isomorphism induces a contravariant natural isomorphism between
the represented Hom short-complex functors. -/
@[stacks 0CQX]
def presentationNatIso {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) : functor Q ≅ functor P :=
  NatIso.ofComponents (fun Z ↦ shortComplexIso Φ Z)
    (shortComplexIso_naturality Φ)

/-- The forward component of `presentationNatIso` is the short-complex precomposition map for
the forward presentation morphism. -/
@[simp]
theorem presentationNatIso_hom_app {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) (Z : D) :
    (presentationNatIso Φ).hom.app Z = shortComplexPrecomp Φ.toHom Z := sorry

/-- The inverse component of `presentationNatIso` is the short-complex precomposition map for
the inverse presentation isomorphism. -/
@[simp]
theorem presentationNatIso_inv_app {K L : ℕ ⥤ D} {e : K ≅ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (Φ : Presentation.Iso e P Q) (Z : D) :
    (presentationNatIso Φ).inv.app Z = shortComplexPrecomp Φ.symm.toHom Z := sorry

end CategoryTheory.HomotopyColimit.RepresentedHom

end
