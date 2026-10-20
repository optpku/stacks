module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.SmoothCompactification
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.56.1: a separated finite-presentation morphism whose fibre over a generic point
of an irreducible component has dimension at most one admits, after shrinking around that point
and making a finite, surjective, universally injective base change, a finite smooth covering
diagram by families admitting proper smooth compactifications with geometrically connected
fibres of dimension at most one. The covering is generically a thickening on a fibrewise dense
open subscheme. -/
@[stacks 0GK7]
#check (AlgebraicGeometry.Scheme.Hom.FinitePresentation.exists_smoothCompactificationDiagram :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [Scheme.Hom.FinitePresentation f]
    (η : S) (hη : η ∈ genericPoints S)
    (hdim : topologicalKrullDim (f.fiber η) ≤ (1 : WithBot ℕ∞)),
    ∃ (U : S.Opens) (_ : η ∈ U)
      (V XU XV : Scheme.{u}) (g : V ⟶ U)
      (_ : IsFinite g) (_ : Surjective g) (_ : UniversallyInjective g)
      (xU : XU ⟶ X) (pU : XU ⟶ U) (_ : IsPullback xU pU f U.ι)
      (xVU : XV ⟶ XU) (pV : XV ⟶ V) (_ : IsPullback xVU pV pU g)
      (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
      (t : ∀ i, T i ⟶ V) (pY : ∀ i, Y i ⟶ T i)
      (pbar : ∀ i, Ybar i ⟶ T i) (j : ∀ i, Y i ⟶ Ybar i)
      (ν : (∐ Y) ⟶ XV)
      (_ : Limits.Sigma.map j ≫ Limits.Sigma.map pbar = Limits.Sigma.map pY)
      (_ : Limits.Sigma.map pY ≫ Limits.Sigma.desc t = ν ≫ pV)
      (_ : IsOpenImmersion (Limits.Sigma.map j))
      (_ : IsFinite ν) (_ : Surjective ν)
      (_ : ∀ i, IsFinite (t i)) (_ : ∀ i, Etale (t i))
      (_ : ∀ i, Surjective (pY i)) (_ : ∀ i, Smooth (pY i))
      (_ : ∀ i, Smooth (pbar i)) (_ : ∀ i, IsProper (pbar i))
      (_ : ∀ i, GeometricallyConnected (pbar i))
      (_ : ∀ i s, topologicalKrullDim ((pbar i).fiber s) ≤ (1 : WithBot ℕ∞))
      (W : XV.Opens)
      (_ : ∀ v : V, Dense ((pV.fiberι v) ⁻¹' (W : Set XV)))
      (_ : ∀ i s, Dense ((pY i).fiberι s ⁻¹'
        ((((Limits.Sigma.ι Y i ≫ ν) ⁻¹ᵁ W) : (Y i).Opens) : Set (Y i)))),
      IsThickening (ν ∣_ W))
