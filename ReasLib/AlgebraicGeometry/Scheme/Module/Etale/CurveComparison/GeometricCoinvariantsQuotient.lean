module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualGaloisModule
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Forward

/-!
# Arithmetic action on geometric coinvariants

Arithmetic translations descend to the geometric coinvariant quotient and make its
canonical projection a morphism of finite discrete arithmetic modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry MonoidAlgebra

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (xbar : GeometricPoint (geometricBaseChange X))
variable (Mρ : (finiteTypeDiscreteModule Λ
    (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))).FullSubcategory)

/-- Arithmetic translation followed by the geometric quotient is invariant under the
geometric monoid-algebra action. -/
theorem geometricCoinvariants_arithmetic_invariant
    (γ : Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar))) :
    let Mgeo := (geometricRestriction X xbar Mρ.obj).obj
    ∀ (g : Aut (GeometricPoint.finiteFiber xbar)) (p : Mgeo.V),
      ((geometricCoinvariants_mk X xbar Mρ.obj).comp (Mρ.obj.obj.ρ γ).hom)
          (@SMul.smul _ _ (moduleOfAction Mgeo).toSMul (MonoidAlgebra.single g (1 : Λ)) p) =
        ((geometricCoinvariants_mk X xbar Mρ.obj).comp (Mρ.obj.obj.ρ γ).hom) p :=
  sorry

/-- Arithmetic translation induces a linear endomorphism of geometric coinvariants. -/
def arithmeticCoinvariantsEnd
    (γ : Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar))) :
    ModuleCat.of Λ (geometricCoinvariantsModule X xbar Mρ.obj) ⟶
      ModuleCat.of Λ (geometricCoinvariantsModule X xbar Mρ.obj) :=
  let Mgeo := (geometricRestriction X xbar Mρ.obj).obj
  ModuleCat.ofHom
    (@MonoidAlgebra.Coinvariants.lift Λ (Aut (GeometricPoint.finiteFiber xbar)) Mgeo.V
      _ _ _ (moduleOfAction Mgeo) _ _ _ _
      ((geometricCoinvariants_mk X xbar Mρ.obj).comp (Mρ.obj.obj.ρ γ).hom)
      (geometricCoinvariants_arithmetic_invariant X xbar Mρ γ))

/-- Descended arithmetic translations satisfy the action laws. -/
theorem arithmeticCoinvariantsEnd_laws :
    arithmeticCoinvariantsEnd X xbar Mρ 1 = 𝟙 _ ∧
      ∀ γ δ : Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)),
        arithmeticCoinvariantsEnd X xbar Mρ (γ * δ) =
          arithmeticCoinvariantsEnd X xbar Mρ δ ≫ arithmeticCoinvariantsEnd X xbar Mρ γ :=
  sorry

/-- The arithmetic fundamental group acts on the geometric coinvariant quotient. -/
def arithmeticCoinvariantsAction :
    Action (ModuleCat.{u + 1} Λ)
      (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar))) where
  V := ModuleCat.of Λ (geometricCoinvariantsModule X xbar Mρ.obj)
  ρ :=
    { toFun := arithmeticCoinvariantsEnd X xbar Mρ
      map_one' := (arithmeticCoinvariantsEnd_laws X xbar Mρ).1
      map_mul' := (arithmeticCoinvariantsEnd_laws X xbar Mρ).2 }

/-- The descended arithmetic action has open stabilizers. -/
theorem arithmeticCoinvariantsAction_isDiscrete :
    openStabilizer Λ (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))
      (arithmeticCoinvariantsAction X xbar Mρ) :=
  sorry

/-- Geometric coinvariants of a finite-type arithmetic module have finite type. -/
theorem arithmeticCoinvariantsAction_finiteType :
    Module.Finite Λ (arithmeticCoinvariantsAction X xbar Mρ).V :=
  sorry

/-- The geometric coinvariant quotient as a finite discrete arithmetic module. -/
def inflationOfGeometricCoinvariants :
    (finiteTypeDiscreteModule Λ
      (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))).FullSubcategory :=
  ⟨⟨arithmeticCoinvariantsAction X xbar Mρ,
    arithmeticCoinvariantsAction_isDiscrete X xbar Mρ⟩,
    arithmeticCoinvariantsAction_finiteType X xbar Mρ⟩

/-- The canonical quotient map of discrete `π₁(X)`-modules from `Mρ` onto geometric
coinvariants, inflated with trivial geometric action. -/
def coinvariantsQuotientHom :
    Mρ.obj.obj ⟶ (inflationOfGeometricCoinvariants X xbar Mρ).obj.obj where
  hom := ModuleCat.ofHom (geometricCoinvariants_mk X xbar Mρ.obj)
  comm := fun _ ↦ sorry

end AlgebraicGeometry.SchemeOverField

end
