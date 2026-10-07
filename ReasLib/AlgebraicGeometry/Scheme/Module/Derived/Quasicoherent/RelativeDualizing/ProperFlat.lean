module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing.Rigidity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ClosedImmersion.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.ClosedImmersion.InternalHom

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDualizingComplex

section

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [CompactSpace S] [QuasiSeparatedSpace S]
variable [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
variable [HomotopyTensorDescends X.toRingedSpace]
variable [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [MonoidalCategory
  (RingedSpace.ModuleDerived (⊤ : (pullback f f).Opens).toScheme.toRingedSpace)]
variable [(RingedSpace.moduleDerivedPushforward (topDiagonal f).toShHom).LaxMonoidal]
variable (H : MonoidalClosed
  (RingedSpace.ModuleDerived (⊤ : (pullback f f).Opens).toScheme.toRingedSpace))
variable (a : DerivedQCoh S ⥤ DerivedQCoh X)
variable (aAdjunction : DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
variable (c : DerivedQCoh (⊤ : (pullback f f).Opens).toScheme ⥤ DerivedQCoh X)
variable (cAdjunction : DerivedQCoh.pushforwardCohomologyIn (topDiagonal f) ⊣ c)
variable (e : DerivedQCoh.structureSheaf X ≅
  c.obj ((DerivedQCoh.pullback
    ((⊤ : (pullback f f).Opens).ι ≫ pullback.fst f f)).obj
      (DerivedQCoh.relativeDualizingComplex f a aAdjunction)))

/-- The map induced by a chosen diagonal-adjunction isomorphism gives an invertible
duality map for the relative dualizing complex. -/
noncomputable instance mapOfAdjointIso_dualityMapIsIso :
    IsIso (dualityMap (topDiagonal f) H
      (mapOfAdjointIso (topDiagonal f) c cAdjunction
          ((DerivedQCoh.pullback
            ((⊤ : (pullback f f).Opens).ι ≫ pullback.fst f f)).obj
              (DerivedQCoh.relativeDualizingComplex f a aAdjunction)) e ≫
        (DerivedQCoh.pullback.inclusionIso
          ((⊤ : (pullback f f).Opens).ι ≫ pullback.fst f f)).hom.app
            (DerivedQCoh.relativeDualizingComplex f a aAdjunction))) := sorry

/-- The derived-quasicoherent relative dualizing complex of a proper flat finitely
presented morphism, equipped with its diagonal-adjunction map. -/
noncomputable def ofDerivedQCoh :
    Scheme.RelativeDualizingComplex f (⊤ : (pullback f f).Opens) (topDiagonal f)
      (topDiagonal_comp_ι f) H :=
  Scheme.RelativeDualizingComplex.of f (⊤ : (pullback f f).Opens) (topDiagonal f)
    (topDiagonal_comp_ι f) H
    (DerivedQCoh.relativeDualizingComplex f a aAdjunction).obj
    (mapOfAdjointIso (topDiagonal f) c cAdjunction
        ((DerivedQCoh.pullback
          ((⊤ : (pullback f f).Opens).ι ≫ pullback.fst f f)).obj
            (DerivedQCoh.relativeDualizingComplex f a aAdjunction)) e ≫
      (DerivedQCoh.pullback.inclusionIso
        ((⊤ : (pullback f f).Opens).ι ≫ pullback.fst f f)).hom.app
          (DerivedQCoh.relativeDualizingComplex f a aAdjunction))
    (DerivedQCoh.relativeDualizingComplex_isPerfectRelativeTo f a aAdjunction)
    (mapOfAdjointIso_dualityMapIsIso f H a aAdjunction c cAdjunction e)

/-- The complex underlying `ofDerivedQCoh` is the relative dualizing complex from the
chosen right adjoint to pushforward. -/
theorem ofDerivedQCoh_complex :
    (ofDerivedQCoh f H a aAdjunction c cAdjunction e).complex =
      (DerivedQCoh.relativeDualizingComplex f a aAdjunction).obj := sorry

/-- The structure map of `ofDerivedQCoh` is induced by the chosen diagonal-adjunction
isomorphism. -/
theorem ofDerivedQCoh_map :
    (ofDerivedQCoh f H a aAdjunction c cAdjunction e).map =
      mapOfAdjointIso (topDiagonal f) c cAdjunction
          ((DerivedQCoh.pullback
            ((⊤ : (pullback f f).Opens).ι ≫ pullback.fst f f)).obj
              (DerivedQCoh.relativeDualizingComplex f a aAdjunction)) e ≫
        (DerivedQCoh.pullback.inclusionIso
          ((⊤ : (pullback f f).Opens).ι ≫ pullback.fst f f)).hom.app
            (DerivedQCoh.relativeDualizingComplex f a aAdjunction) := sorry

/-- `ofDerivedQCoh` satisfies relative perfectness and invertibility of its induced
duality map. -/
theorem ofDerivedQCoh_spec :
    ModuleDerived.IsPerfectRelativeTo f
        (ofDerivedQCoh f H a aAdjunction c cAdjunction e).complex ∧
      IsIso (dualityMap (topDiagonal f) H
        (ofDerivedQCoh f H a aAdjunction c cAdjunction e).map) := sorry

end

end AlgebraicGeometry.Scheme.RelativeDualizingComplex
