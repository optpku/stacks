module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

universe u

#check (AlgebraicGeometry.SchemeOverField.genus : ∀ {k : Type u} [Field k]
  (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.IsProper X.hom],
  (topologicalKrullDim X.left = 1) →
  Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom) → ℕ)

#check (AlgebraicGeometry.SchemeOverField.genus_def : ∀ {k : Type u} [Field k]
  (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.IsProper X.hom]
  (h_dimension : topologicalKrullDim X.left = 1)
  (hΓ : Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom)),
  AlgebraicGeometry.SchemeOverField.genus X h_dimension hΓ =
    AlgebraicGeometry.Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)

#check (AlgebraicGeometry.SchemeOverField.genus_proof_irrel : ∀ {k : Type u} [Field k]
  (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.IsProper X.hom]
  (h_dimension h_dimension' : topologicalKrullDim X.left = 1)
  (hΓ hΓ' : Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom)),
  AlgebraicGeometry.SchemeOverField.genus X h_dimension hΓ =
    AlgebraicGeometry.SchemeOverField.genus X h_dimension' hΓ')
