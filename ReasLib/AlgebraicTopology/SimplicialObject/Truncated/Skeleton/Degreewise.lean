module

public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteConnected
public import ReasLib.CategoryTheory.Functor.LeftKanExtension.ColimitMap
public import ReasLib.CategoryTheory.Functor.KanExtension.AtImage
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 018L

# Degreewise coordinates for simplicial skeleta

This file specializes the canonical pointwise left-Kan-extension coordinates to the chosen
objectwise skeleton of a truncated simplicial object. The definitions are abbreviations of the
generic owners; the namespace hides the repeated truncated-simplex inclusion and
costructured-arrow diagram from downstream statements.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Truncated.skeleton.degree

variable {C : Type u} [Category.{v} C]

/-- The costructured-arrow category indexing the value of an `m`-skeleton at `Delta`. -/
@[stacks 018L "degreewise skeleton index"]
abbrev Index (m : ℕ) (Delta : SimplexCategory) :=
  CostructuredArrow (SimplexCategory.Truncated.inclusion m).op (op Delta)

namespace Index

/-- A simplex morphism reindexes the costructured arrows used in the skeleton colimit. -/
@[stacks 018L "degreewise skeleton index reindexing"]
abbrev map {m : ℕ} {Delta Delta' : SimplexCategory} (f : Delta ⟶ Delta') :
    Index m Delta' ⥤ Index m Delta :=
  CostructuredArrow.map f.op

end Index

/-- The pointwise colimit diagram computing the value of `U.skeleton` at `Delta`. -/
@[stacks 018L "degreewise skeleton diagram"]
abbrev diagram {m : ℕ} (U : SimplicialObject.Truncated C m)
    (Delta : SimplexCategory) : Index m Delta ⥤ C :=
  CostructuredArrow.proj (SimplexCategory.Truncated.inclusion m).op (op Delta) ⋙ U

namespace inRange

/-- The costructured-arrow category at a degree equipped with a proof that it lies in the
truncation range. Keeping the proof in the index exposes the canonical colimit instance. -/
@[stacks 018M "in-range degreewise skeleton index"]
abbrev Index (m n : ℕ) (hn : n ≤ m) :=
  CostructuredArrow
    (SimplexCategory.Truncated.inclusion m).op
    ((SimplexCategory.Truncated.inclusion m).op.obj (op ⦋n, hn⦌ₘ))

/-- The skeleton colimit diagram at a degree equipped with its truncation-range proof. -/
@[stacks 018M "in-range degreewise skeleton diagram"]
abbrev diagram {m n : ℕ} (U : SimplicialObject.Truncated C m) (hn : n ≤ m) :
    Index m n hn ⥤ C :=
  CostructuredArrow.proj
      (SimplexCategory.Truncated.inclusion m).op
      ((SimplexCategory.Truncated.inclusion m).op.obj (op ⦋n, hn⦌ₘ)) ⋙ U

/-- In a degree within the truncation range, the original truncated degree is canonically
isomorphic to the colimit computing the skeleton. -/
@[stacks 018M "degreewise skeleton colimit within the truncation range"]
noncomputable abbrev iso {m n : ℕ} (U : SimplicialObject.Truncated C m) (hn : n ≤ m) :
    U.obj (op ⦋n, hn⦌ₘ) ≅ colimit (inRange.diagram U hn) :=
  Functor.LeftKanExtension.AtImage.iso
    (SimplexCategory.Truncated.inclusion m).op U (op ⦋n, hn⦌ₘ)

/-- The forward map of the in-range skeleton coordinate is the injection indexed by the identity
costructured arrow. -/
@[simp, stacks 018M "in-range skeleton coordinate on the identity injection"]
theorem iso.hom {m n : ℕ} (U : SimplicialObject.Truncated C m) (hn : n ≤ m) :
    (iso U hn).hom =
      colimit.ι (inRange.diagram U hn)
        (CostructuredArrow.mk
          (𝟙 ((SimplexCategory.Truncated.inclusion m).op.obj (op ⦋n, hn⦌ₘ)))) := sorry

/-- Any injection into the in-range skeleton colimit followed by the inverse coordinate applies
the truncated object to the unique preimage of that costructured-arrow leg. -/
@[reassoc (attr := simp), stacks 018M "in-range skeleton coordinate on every injection"]
theorem iso.ι_inv {m n : ℕ} (U : SimplicialObject.Truncated C m) (hn : n ≤ m)
    (g : inRange.Index m n hn) :
    colimit.ι (inRange.diagram U hn) g ≫ (iso U hn).inv =
      U.map ((SimplexCategory.Truncated.inclusion m).op.preimage g.hom) := sorry

end inRange

/-- The canonical coordinate identifying a skeleton value with its pointwise colimit. -/
@[stacks 018L "degreewise skeleton colimit coordinate"]
noncomputable abbrev isoColimit {m : ℕ}
    (U : SimplicialObject.Truncated C m) [U.HasPointwiseSkeleton]
    (Delta : SimplexCategory) :
    U.skeleton.obj (op Delta) ≅ colimit (diagram U Delta) :=
  (SimplexCategory.Truncated.inclusion m).op.leftKanExtensionObjIsoColimit U (op Delta)

namespace inRange

/-- The in-range colimit coordinate followed by the inverse chosen skeleton coordinate is the
component of the objectwise left-Kan-extension unit. -/
@[simp, stacks 018M "in-range skeleton coordinate as the left Kan extension unit"]
theorem iso.unit {m n : ℕ} (U : SimplicialObject.Truncated C m)
    [U.HasPointwiseSkeleton] (hn : n ≤ m) :
    (iso U hn).hom ≫ (isoColimit U ⦋n⦌).inv =
      ((SimplexCategory.Truncated.inclusion m).op.leftKanExtensionUnit U).app
        (op ⦋n, hn⦌ₘ) := sorry

end inRange

/-- The map between degreewise skeleton colimits induced by a simplex morphism. This is the
endpoint-minimal `LeftKanExtension.colimitMap` specialization. -/
@[stacks 018L "map between degreewise skeleton colimits"]
noncomputable abbrev colimitMap {m : ℕ} (U : SimplicialObject.Truncated C m)
    {Delta Delta' : SimplexCategory} (f : Delta ⟶ Delta')
    [HasColimit (diagram U Delta')]
    [HasColimit (diagram U Delta)] :
    colimit (diagram U Delta') ⟶ colimit (diagram U Delta) :=
  Functor.LeftKanExtension.colimitMap
    (SimplexCategory.Truncated.inclusion m).op U f.op

/-- The degreewise colimit map sends an injection to the injection indexed by the reindexed
costructured arrow. -/
@[reassoc (attr := simp), stacks 018L "degreewise skeleton colimit map on injections"]
theorem colimitMap.ι {m : ℕ} (U : SimplicialObject.Truncated C m)
    {Delta Delta' : SimplexCategory} (f : Delta ⟶ Delta') (g : Index m Delta')
    [HasColimit (diagram U Delta')]
    [HasColimit (diagram U Delta)] :
    colimit.ι (diagram U Delta') g ≫ colimitMap U f =
      colimit.ι (diagram U Delta) ((Index.map f).obj g) := sorry

/-- The degreewise colimit map associated to an identity is the identity. -/
@[simp, stacks 018L "identity law for degreewise skeleton colimit maps"]
theorem colimitMap.id {m : ℕ} (U : SimplicialObject.Truncated C m)
    (Delta : SimplexCategory) [HasColimit (diagram U Delta)] :
    colimitMap U (𝟙 Delta) = 𝟙 (colimit (diagram U Delta)) := sorry

/-- Degreewise skeleton colimit maps respect composition, with the order reversed by
contravariance in the simplex category. -/
@[stacks 018L "composition law for degreewise skeleton colimit maps"]
theorem colimitMap.comp {m : ℕ} (U : SimplicialObject.Truncated C m)
    {Delta Delta' Delta'' : SimplexCategory}
    (f : Delta ⟶ Delta') (g : Delta' ⟶ Delta'')
    [HasColimit (diagram U Delta'')]
    [HasColimit (diagram U Delta')]
    [HasColimit (diagram U Delta)] :
    colimitMap U (f ≫ g) = colimitMap U g ≫ colimitMap U f := sorry

namespace isoColimit

/-- A colimit injection followed by the inverse skeleton coordinate is the leg determined by
the left-Kan-extension unit and its indexing arrow. -/
@[reassoc (attr := simp), stacks 018L "inverse degreewise skeleton coordinate"]
theorem injection_inv {m : ℕ}
    (U : SimplicialObject.Truncated C m) [U.HasPointwiseSkeleton]
    {Delta : SimplexCategory}
    (g : Index m Delta) :
    colimit.ι (diagram U Delta) g ≫ (isoColimit U Delta).inv =
      ((SimplexCategory.Truncated.inclusion m).op.leftKanExtensionUnit U).app g.left ≫
        U.skeleton.map g.hom := sorry

/-- The forward skeleton coordinate sends the left-Kan-extension leg at a costructured arrow to
the corresponding colimit injection. -/
@[reassoc (attr := simp), stacks 018L "forward degreewise skeleton coordinate"]
theorem injection_hom {m : ℕ}
    (U : SimplicialObject.Truncated C m) [U.HasPointwiseSkeleton]
    {Delta : SimplexCategory}
    (g : Index m Delta) :
    ((SimplexCategory.Truncated.inclusion m).op.leftKanExtensionUnit U).app g.left ≫
          U.skeleton.map g.hom ≫
        (isoColimit U Delta).hom =
      colimit.ι (diagram U Delta) g := sorry

/-- In canonical degreewise colimit coordinates, the skeleton structure map is induced by
reindexing costructured arrows. -/
@[stacks 018L "skeleton structure map in degreewise colimit coordinates"]
theorem map {m : ℕ}
    (U : SimplicialObject.Truncated C m) [U.HasPointwiseSkeleton]
    {Delta Delta' : SimplexCategory}
    (f : Delta ⟶ Delta') :
    (isoColimit U Delta').inv ≫
          U.skeleton.map f.op ≫
        (isoColimit U Delta).hom =
      colimitMap U f := sorry

/-- In canonical degreewise colimit coordinates, a skeleton structure map sends an injection to
the injection indexed by the reindexed costructured arrow. -/
@[stacks 018L "skeleton structure map on degreewise colimit injections"]
theorem injection_map {m : ℕ}
    (U : SimplicialObject.Truncated C m) [U.HasPointwiseSkeleton]
    {Delta Delta' : SimplexCategory}
    (f : Delta ⟶ Delta') (g : Index m Delta') :
    colimit.ι (diagram U Delta') g ≫
          (isoColimit U Delta').inv ≫
          U.skeleton.map f.op ≫
        (isoColimit U Delta).hom =
      colimit.ι (diagram U Delta) ((Index.map f).obj g) := sorry

end isoColimit

end CategoryTheory.SimplicialObject.Truncated.skeleton.degree
