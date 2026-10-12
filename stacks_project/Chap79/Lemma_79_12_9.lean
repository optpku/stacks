/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap79.Lemma_79_12_9_Sheaf

/-!
# Fibre products of finite-part sheaves
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 79.12.9: Let `S` be a scheme. Let `pX : X' ⟶ X`, `fX' : X' ⟶ Y'`,
`fX : X ⟶ Y`, and `pY : Y' ⟶ Y` be a fibre product square of algebraic spaces
over `S`. Then the square of sheaves on `Scheme.fppfTopology.over S` with
vertices `finitePartSheaf fX'`, `finitePartSheaf fX`, `(toFppfSheaf S).obj Y'`,
and `(toFppfSheaf S).obj Y`, and with edges `finitePartMap h`,
`finitePartTo fX'`, `finitePartTo fX`, and `(toFppfSheaf S).map pY`, is a
fibre product square. -/
@[stacks 04QF]
theorem finitePart_isPullback {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY) :
    IsPullback (finitePartMap h) (finitePartTo fX') (finitePartTo fX)
      ((toFppfSheaf S).map pY) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
