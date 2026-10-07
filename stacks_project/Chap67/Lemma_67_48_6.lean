module

public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_48_6_Reduced

/-!
# Reducedness of relative normalizations of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 67.48.6: let `S` be a scheme, and let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`. If `X` is reduced, then the
relative normalization `normalization f` of `Y` in `X` is reduced.

In Stacks language, `f : Y ⟶ X` and `X'` are Lean `f : X ⟶ Y` and
`Hom.normalization f`, and reducedness of `Y` is `[IsReduced X]`. -/
@[stacks 0AYF]
instance instIsReducedNormalization {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [IsReduced X] :
    IsReduced (normalization f) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
