/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.CategoryTheory.Functor.RightKanExtension.LimitMap
public import ReasLib.CategoryTheory.Functor.KanExtension.AtImage
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0183

# Degreewise coordinates for simplicial coskeleta

This file specializes the canonical pointwise right-Kan-extension coordinates to the objectwise
coskeleton of a truncated simplicial object. The definitions are abbreviations of the generic
owners; the namespace only hides the repeated truncated-simplex inclusion and structured-arrow
diagram from downstream statements.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Truncated.coskeleton.degree

variable {C : Type u} [Category.{v} C]

/-- The structured-arrow category indexing the value of an `m`-coskeleton at `Delta`. -/
@[stacks 0183 "degreewise coskeleton index"]
abbrev Index (m : ℕ) (Delta : SimplexCategory) :=
  StructuredArrow (op Delta) (SimplexCategory.Truncated.inclusion m).op

namespace Index

/-- A simplex morphism reindexes the structured arrows used in the coskeleton limit. -/
@[stacks 0183 "degreewise coskeleton index reindexing"]
abbrev map {m : ℕ} {Delta Delta' : SimplexCategory} (f : Delta ⟶ Delta') :
    Index m Delta ⥤ Index m Delta' :=
  StructuredArrow.map f.op

end Index

/-- The pointwise limit diagram computing the value of `U.coskeleton` at `Delta`. -/
@[stacks 0183 "degreewise coskeleton diagram"]
abbrev diagram {m : ℕ} (U : SimplicialObject.Truncated C m)
    (Delta : SimplexCategory) : Index m Delta ⥤ C :=
  StructuredArrow.proj (op Delta) (SimplexCategory.Truncated.inclusion m).op ⋙ U

namespace inRange

/-- The structured-arrow category at a degree equipped with a proof that it lies in the
truncation range. Keeping the proof in the index exposes the canonical limit instance. -/
@[stacks 0184 "in-range degreewise coskeleton index"]
abbrev Index (m n : ℕ) (hn : n ≤ m) :=
  StructuredArrow
    ((SimplexCategory.Truncated.inclusion m).op.obj (op ⦋n, hn⦌ₘ))
    (SimplexCategory.Truncated.inclusion m).op

/-- The coskeleton limit diagram at a degree equipped with its truncation-range proof. -/
@[stacks 0184 "in-range degreewise coskeleton diagram"]
abbrev diagram {m n : ℕ} (U : SimplicialObject.Truncated C m) (hn : n ≤ m) :
    Index m n hn ⥤ C :=
  StructuredArrow.proj
      ((SimplexCategory.Truncated.inclusion m).op.obj (op ⦋n, hn⦌ₘ))
      (SimplexCategory.Truncated.inclusion m).op ⋙ U

/-- In a degree within the truncation range, the limit computing the coskeleton is canonically
isomorphic to the original truncated degree. -/
@[stacks 0184 "degreewise coskeleton limit within the truncation range"]
noncomputable abbrev iso {m n : ℕ} (U : SimplicialObject.Truncated C m) (hn : n ≤ m) :
    limit (inRange.diagram U hn) ≅ U.obj (op ⦋n, hn⦌ₘ) :=
  Functor.RightKanExtension.AtImage.iso
    (SimplexCategory.Truncated.inclusion m).op U (op ⦋n, hn⦌ₘ)

/-- The forward map of the in-range coskeleton coordinate is the projection indexed by the
identity structured arrow. -/
@[simp, stacks 0184 "in-range coskeleton coordinate on the identity projection"]
theorem iso.hom {m n : ℕ} (U : SimplicialObject.Truncated C m) (hn : n ≤ m) :
    (iso U hn).hom =
      limit.π (inRange.diagram U hn)
        (StructuredArrow.mk
          (𝟙 ((SimplexCategory.Truncated.inclusion m).op.obj (op ⦋n, hn⦌ₘ)))) := sorry

/-- The inverse in-range coskeleton coordinate followed by any projection applies the truncated
object to the unique preimage of that structured-arrow leg. -/
@[reassoc (attr := simp), stacks 0184 "in-range coskeleton coordinate on every projection"]
theorem iso.inv_π {m n : ℕ} (U : SimplicialObject.Truncated C m) (hn : n ≤ m)
    (g : inRange.Index m n hn) :
    (iso U hn).inv ≫ limit.π (inRange.diagram U hn) g =
      U.map ((SimplexCategory.Truncated.inclusion m).op.preimage g.hom) := sorry

end inRange

/-- The canonical coordinate identifying an objectwise coskeleton value with its pointwise
limit. -/
@[stacks 0183 "degreewise coskeleton limit coordinate"]
noncomputable abbrev isoLimit {m : ℕ}
    (U : SimplicialObject.Truncated C m) [U.HasPointwiseCoskeleton]
    (Delta : SimplexCategory) :
    (U.coskeleton).obj (op Delta) ≅ limit (diagram U Delta) :=
  Functor.RightKanExtension.objIsoLimit
    (SimplexCategory.Truncated.inclusion m).op U (op Delta)

namespace inRange

/-- The chosen coskeleton limit coordinate followed by the in-range coordinate is the component
of the objectwise right-Kan-extension counit. -/
@[simp, stacks 0184 "in-range coskeleton coordinate as the right Kan extension counit"]
theorem iso.counit {m n : ℕ} (U : SimplicialObject.Truncated C m)
    [U.HasPointwiseCoskeleton] (hn : n ≤ m) :
    (isoLimit U ⦋n⦌).hom ≫ (iso U hn).hom =
      ((SimplexCategory.Truncated.inclusion m).op.rightKanExtensionCounit U).app
        (op ⦋n, hn⦌ₘ) := sorry

end inRange

/-- The map between degreewise objectwise-coskeleton limits induced by a simplex morphism. This
is the endpoint-minimal `RightKanExtension.limitMap` specialization. -/
@[stacks 0183 "map between degreewise coskeleton limits"]
noncomputable abbrev limitMap {m : ℕ} (U : SimplicialObject.Truncated C m)
    {Delta Delta' : SimplexCategory} (f : Delta ⟶ Delta')
    [HasLimit (diagram U Delta')]
    [HasLimit (diagram U Delta)] :
    limit (diagram U Delta') ⟶ limit (diagram U Delta) :=
  Functor.RightKanExtension.limitMap
    (SimplexCategory.Truncated.inclusion m).op U f.op

/-- The degreewise limit map followed by a projection is the projection indexed by the
reindexed structured arrow. -/
@[reassoc (attr := simp), stacks 0183 "degreewise coskeleton limit map on projections"]
theorem limitMap.π {m : ℕ} (U : SimplicialObject.Truncated C m)
    {Delta Delta' : SimplexCategory} (f : Delta ⟶ Delta') (g : Index m Delta)
    [HasLimit (diagram U Delta')]
    [HasLimit (diagram U Delta)] :
    limitMap U f ≫ limit.π (diagram U Delta) g =
      limit.π (diagram U Delta') ((Index.map f).obj g) := sorry

/-- The degreewise objectwise-coskeleton limit map associated to an identity is the identity. -/
@[simp, stacks 0183 "identity law for degreewise coskeleton limit maps"]
theorem limitMap.id {m : ℕ} (U : SimplicialObject.Truncated C m)
    (Delta : SimplexCategory) [HasLimit (diagram U Delta)] :
    limitMap U (𝟙 Delta) = 𝟙 (limit (diagram U Delta)) := sorry

/-- Degreewise objectwise-coskeleton limit maps send composition of simplex morphisms to
composition in the reverse order. -/
@[stacks 0183 "composition law for degreewise coskeleton limit maps"]
theorem limitMap.comp {m : ℕ} (U : SimplicialObject.Truncated C m)
    {Delta Delta' Delta'' : SimplexCategory}
    (f : Delta ⟶ Delta') (g : Delta' ⟶ Delta'')
    [HasLimit (diagram U Delta'')]
    [HasLimit (diagram U Delta')]
    [HasLimit (diagram U Delta)] :
    limitMap U (f ≫ g) = limitMap U g ≫ limitMap U f := sorry

namespace isoLimit

/-- The forward degreewise coskeleton coordinate computes through the right Kan extension
counit at every structured arrow. -/
@[reassoc (attr := simp), stacks 0183 "degreewise coskeleton coordinate on projections"]
theorem hom_π {m : ℕ}
    (U : SimplicialObject.Truncated C m) [U.HasPointwiseCoskeleton]
    {Delta : SimplexCategory}
    (g : Index m Delta) :
    (isoLimit U Delta).hom ≫ limit.π (diagram U Delta) g =
      (U.coskeleton).map g.hom ≫
        ((SimplexCategory.Truncated.inclusion m).op.rightKanExtensionCounit U).app
          g.right := sorry

/-- The inverse degreewise coskeleton coordinate recovers every limit projection from the
objectwise right-Kan-extension counit. -/
@[reassoc (attr := simp), stacks 0183 "inverse degreewise coskeleton coordinate"]
theorem inv_π {m : ℕ}
    (U : SimplicialObject.Truncated C m) [U.HasPointwiseCoskeleton]
    {Delta : SimplexCategory} (g : Index m Delta) :
    (isoLimit U Delta).inv ≫ (U.coskeleton).map g.hom ≫
        ((SimplexCategory.Truncated.inclusion m).op.rightKanExtensionCounit U).app
          g.right =
      limit.π (diagram U Delta) g := sorry

/-- In canonical degreewise limit coordinates, the coskeleton structure map is the map induced
by reindexing structured arrows. -/
@[stacks 0183 "coskeleton structure map in degreewise limit coordinates"]
theorem map {m : ℕ}
    (U : SimplicialObject.Truncated C m) [U.HasPointwiseCoskeleton]
    {Delta Delta' : SimplexCategory}
    (f : Delta ⟶ Delta') :
    (isoLimit U Delta').inv ≫
          (U.coskeleton).map f.op ≫
        (isoLimit U Delta).hom =
      limitMap U f := sorry

/-- In canonical degreewise limit coordinates, a coskeleton structure map followed by a
projection is the projection indexed by the reindexed structured arrow. -/
@[stacks 0183 "coskeleton structure map on degreewise limit projections"]
theorem map_π {m : ℕ}
    (U : SimplicialObject.Truncated C m) [U.HasPointwiseCoskeleton]
    {Delta Delta' : SimplexCategory}
    (f : Delta ⟶ Delta') (g : Index m Delta) :
    (isoLimit U Delta').inv ≫
          (U.coskeleton).map f.op ≫
          (isoLimit U Delta).hom ≫
        limit.π (diagram U Delta) g =
      limit.π (diagram U Delta') ((Index.map f).obj g) := sorry

end isoLimit

end CategoryTheory.SimplicialObject.Truncated.coskeleton.degree
