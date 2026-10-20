module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Finite

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.IsFinite :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.QcAlgebraUnder → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.isFinite_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.IsFinite A ↔
      ∀ U : AlgebraicGeometry.AlgebraicSpace.affineEtaleSite X,
        Module.Finite Γ(U.obj.left.left, ⊤)
          (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.sectionRing A U.obj))

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.instIsFinite_structureQcAlgebra :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.IsFinite
      (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.structureQcAlgebra X))

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteProperty :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    ObjectProperty (Under (AlgebraicGeometry.AlgebraicSpace.commStructureSheaf X)))

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteProperty_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Under (AlgebraicGeometry.AlgebraicSpace.commStructureSheaf X)),
    AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteProperty X B ↔
      ∃ h : AlgebraicGeometry.AlgebraicSpace.qcAlgebraUnderProperty X B,
        AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.IsFinite ⟨B, h⟩)

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteProperty_obj :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder),
    AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteProperty X A.obj ↔
      AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.IsFinite A)

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.exists_finite_finitelyPresentable_colimitPresentation_locallySurjective :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder)
      [AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.IsFinite A],
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ pres : ColimitPresentation I A.obj,
        (∀ i : I,
          AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteProperty X (pres.diag.obj i)) ∧
          (∀ i : I,
            AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finitelyPresentableProperty X
              (pres.diag.obj i)) ∧
            ∀ {i i' : I} (f : i ⟶ i'),
              Sheaf.IsLocallySurjective (pres.diag.map f).right)

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.exists_finite_finitelyPresentable_locallySurjective :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder)
      [AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.IsFinite A],
    ∃ (B : X.QcAlgebraUnder)
      (_ : AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.IsFinite B)
      (_ : AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.IsFinitePresentation B)
      (f : B.obj ⟶ A.obj), Sheaf.IsLocallySurjective f.right)

end
