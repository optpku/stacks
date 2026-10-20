module

public import ReasLib.AlgebraicGeometry.GroupScheme.Torsor

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- The generic precoverage torsor API remains available through this compatibility module. -/
#check (AlgebraicGeometry.GroupScheme.isTorsorFor_iff :
  ∀ {S : Scheme.{u}} (G : Grp (Over S)) (X : Mod (Over S) G.X)
      (K : Precoverage Scheme.{u}),
    AlgebraicGeometry.GroupScheme.IsTorsorFor G X K ↔
      Mod.IsPseudoTorsor X ∧
        ∃ U : S.Cover.{u} K,
          ∀ i : U.I₀, Nonempty ((Over.mk (U.f i) : Over S) ⟶ X.X))
