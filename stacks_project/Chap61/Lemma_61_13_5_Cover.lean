module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import ReasLib.CategoryTheory.Sites.MorphismProperty.Covering
public import stacks_project.Chap61.Definition_61_12_8_Presentation

/-!
# Singleton weakly contractible covers in the pro-étale topology

Every object of the big, small, or slice pro-étale site admits a singleton
covering by a weakly contractible object. If the target is quasi-compact, that
covering object may be taken affine.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.Proetale

/-- Every scheme admits a singleton covering arrow in the pro-étale topology
whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible (U : Scheme.{u}) :
    ∃ (V : Scheme.{u}) (f : V ⟶ U),
      Scheme.proetaleTopology.coveringArrows f ∧
        Scheme.proetaleTopology.IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact scheme admits a singleton covering arrow in the
pro-étale topology whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible (U : Scheme.{u})
    [CompactSpace U] :
    ∃ (V : Scheme.{u}) (f : V ⟶ U),
      Scheme.proetaleTopology.coveringArrows f ∧
        IsAffine V ∧ Scheme.proetaleTopology.IsWeaklyContractible V :=
  sorry

/-- Every scheme over `S` admits a singleton covering arrow in the slice
pro-étale topology whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible_over (S : Scheme.{u})
    (U : Over S) :
    ∃ (V : Over S) (f : V ⟶ U),
      (Scheme.proetaleTopology.over S).coveringArrows f ∧
        (Scheme.proetaleTopology.over S).IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact scheme over `S` admits a singleton covering arrow in
the slice pro-étale topology whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible_over (S : Scheme.{u})
    (U : Over S) [CompactSpace U.left] :
    ∃ (V : Over S) (f : V ⟶ U),
      (Scheme.proetaleTopology.over S).coveringArrows f ∧
        IsAffine V.left ∧
          (Scheme.proetaleTopology.over S).IsWeaklyContractible V :=
  sorry

/-- Every scheme admits a singleton family covering in the pro-étale
precoverage whose source is weakly contractible. -/
theorem exists_singleton_mem_proetalePrecoverage (U : Scheme.{u}) :
    ∃ (V : Scheme.{u}) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          Scheme.proetalePrecoverage U ∧
        Scheme.proetaleTopology.IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact scheme admits a singleton family covering in the
pro-étale precoverage whose source is affine and weakly contractible. -/
theorem exists_singleton_mem_proetalePrecoverage_isAffine (U : Scheme.{u})
    [CompactSpace U] :
    ∃ (V : Scheme.{u}) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          Scheme.proetalePrecoverage U ∧
        IsAffine V ∧ Scheme.proetaleTopology.IsWeaklyContractible V :=
  sorry

end AlgebraicGeometry.Scheme.Proetale

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every object of the small pro-étale site of `S` admits a singleton covering
arrow whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible (S : Scheme.{u}) (U : S.ProEt) :
    ∃ (V : S.ProEt) (f : V ⟶ U),
      (topology S).coveringArrows f ∧ (topology S).IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact object of the small pro-étale site of `S` admits a
singleton covering arrow whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible (S : Scheme.{u})
    (U : S.ProEt) [CompactSpace U.left] :
    ∃ (V : S.ProEt) (f : V ⟶ U),
      (topology S).coveringArrows f ∧
        IsAffine V.left ∧ (topology S).IsWeaklyContractible V :=
  sorry

/-- Every object of the small pro-étale site of `S` admits a singleton family
covering in the small pro-étale precoverage whose source is weakly
contractible. -/
theorem exists_singleton_mem_precoverage (S : Scheme.{u}) (U : S.ProEt) :
    ∃ (V : S.ProEt) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          precoverage S U ∧
        (topology S).IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact object of the small pro-étale site of `S` admits a
singleton family covering in the small pro-étale precoverage whose source is
affine and weakly contractible. -/
theorem exists_singleton_mem_precoverage_isAffine (S : Scheme.{u}) (U : S.ProEt)
    [CompactSpace U.left] :
    ∃ (V : S.ProEt) (f : V ⟶ U),
      (SemiRepresentableFamily.OverFamily.singleton f).toPresieve ∈
          precoverage S U ∧
        IsAffine V.left ∧ (topology S).IsWeaklyContractible V :=
  sorry

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- Every object of a chosen big pro-étale site admits a singleton covering
arrow whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible
    (X : ChosenBigProetaleSite.{u, v}) (T : X.carrier) :
    ∃ (V : X.carrier) (f : V ⟶ T),
      X.toGrothendieck.coveringArrows f ∧
        X.toGrothendieck.IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact object of a chosen big pro-étale site admits a singleton
covering arrow whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible
    (X : ChosenBigProetaleSite.{u, v}) (T : X.carrier)
    [CompactSpace (X.toScheme.obj T)] :
    ∃ (V : X.carrier) (f : V ⟶ T),
      X.toGrothendieck.coveringArrows f ∧
        IsAffine (X.toScheme.obj V) ∧
          X.toGrothendieck.IsWeaklyContractible V :=
  sorry

/-- Every object of a chosen big pro-étale slice admits a singleton covering
arrow whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible_big
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) (U : Over S) :
    ∃ (V : Over S) (f : V ⟶ U),
      (bigTopology X S).coveringArrows f ∧
        (bigTopology X S).IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact object of a chosen big pro-étale slice admits a singleton
covering arrow whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible_big
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) (U : Over S)
    [CompactSpace (X.toScheme.obj U.left)] :
    ∃ (V : Over S) (f : V ⟶ U),
      (bigTopology X S).coveringArrows f ∧
        IsAffine (X.toScheme.obj V.left) ∧
          (bigTopology X S).IsWeaklyContractible V :=
  sorry

/-- Every object of a chosen small pro-étale site admits a singleton covering
arrow whose source is weakly contractible. -/
theorem exists_coveringArrow_isWeaklyContractible_small
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) (U : smallSite X S) :
    ∃ (V : smallSite X S) (f : V ⟶ U),
      (smallTopology X S).coveringArrows f ∧
        (smallTopology X S).IsWeaklyContractible V :=
  sorry

/-- Every quasi-compact object of a chosen small pro-étale site admits a
singleton covering arrow whose source is affine and weakly contractible. -/
theorem exists_coveringArrow_isAffine_isWeaklyContractible_small
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) (U : smallSite X S)
    [CompactSpace (X.toScheme.obj U.obj.left)] :
    ∃ (V : smallSite X S) (f : V ⟶ U),
      (smallTopology X S).coveringArrows f ∧
        IsAffine (X.toScheme.obj V.obj.left) ∧
          (smallTopology X S).IsWeaklyContractible V :=
  sorry

end AlgebraicGeometry.ChosenBigProetaleSite
