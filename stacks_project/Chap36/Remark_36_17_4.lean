module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Perfect.Generation
import StacksCheckRecall

@[expose] public section

universe u

/- Remark 36.17.4 (1): if `X` is quasi-compact and quasi-separated and `T` has
quasi-compact complement, then `D_QCoh,T(𝒪_X)` has a perfect weak generator. -/
@[stacks 0GEG] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.exists_isPerfect_isWeakGenerator :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (T : TopologicalSpace.Closeds X) (hT : IsCompact (T.compl : Set X)),
      ∃ P : AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn X T,
        AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect P.obj.obj ∧
          CategoryTheory.IsWeakGenerator P)

/- Remark 36.17.4 (2): a perfect weak generator of `D_QCoh,T(𝒪_X)` classically
generates its compact, equivalently perfect, objects. -/
@[stacks 0GEG] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.isClassicalGeneratorOfCompacts :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (T : TopologicalSpace.Closeds X) (hT : IsCompact (T.compl : Set X))
      (G : AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn X T),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect G.obj.obj →
        CategoryTheory.IsWeakGenerator G →
          CategoryTheory.IsClassicalGeneratorOfCompacts G)
