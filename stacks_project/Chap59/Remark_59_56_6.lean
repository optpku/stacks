/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.FieldTheory.Galois.AlgebraicallyClosed
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GeometricPointSections

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Remark 59.56.6: the geometric stalk functor is naturally inverse image along the
geometric point followed by sections over the spectrum of its algebraically closed field. -/
@[stacks 04JN] #check (AlgebraicGeometry.Scheme.Etale.stalkFunctorIsoPullback :
  ∀ {S : Scheme.{u}} (s : GeometricPoint S)
    [HasWeakSheafify (Spec (.of s.K)).smallEtaleTopology (Type u)]
    [∀ P : S.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback s.hom).op.HasLeftKanExtension P],
    Etale.stalkFunctor s ≅ Etale.pullbackThenSections s)

#check (Field.absoluteGaloisGroup_subsingleton :
  ∀ (K : Type u) [Field K] [IsAlgClosed K], Subsingleton (Field.absoluteGaloisGroup K))

#check (AlgebraicGeometry.Scheme.Etale.etaleSheavesEquivType :
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology (Type u)],
    Sheaf (Spec (.of K)).smallEtaleTopology (Type u) ≌ Type u)

#check (AlgebraicGeometry.Scheme.Etale.etaleSheavesEquivType_functor_obj :
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology (Type u)]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)),
    (Etale.etaleSheavesEquivType K).functor.obj F =
      F.obj.obj (Opposite.op (MorphismProperty.Over.mk _ (𝟙 (Spec (.of K))) inferInstance :
        (Spec (.of K)).Etale)))
