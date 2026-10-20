module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Support.Generation

/-!
# Classical generators of perfect supported quasicoherent complexes

A perfect weak generator of `D_QCoh,T(𝒪_X)` on a quasi-compact and quasi-separated
algebraic space, for a closed subset `T` with quasi-compact complement, classically
generates the perfect objects.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.quasiCoherentSupportedOn_isTriangulated :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Set (Points X)),
      (DerivedQCoh.quasiCoherentSupportedOn X T).IsTriangulated)

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.hasCoproducts :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Set (Points X)),
      HasCoproducts.{u} (DerivedQCoh.SupportedOn X T))

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.isClassicalGeneratorOfPerfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (T : Closeds (Points X)),
      IsCompact (T.compl : Set (Points X)) →
        ∀ (G : DerivedQCoh.SupportedOn X (T : Set (Points X))),
          ModuleDerived.IsPerfect G.obj →
            CategoryTheory.IsWeakGenerator G →
              (fun E : DerivedQCoh.SupportedOn X (T : Set (Points X)) ↦
                ModuleDerived.IsPerfect E.obj) ≤
                (CategoryTheory.ObjectProperty.singleton G).triangEnvelope)
