module

public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Automorphism
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Endpoint.Conjugation
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.StrongTrans

/-!
# Canonical Hom-sheaf API

Compatibility aggregate for canonical Hom-sheaf support. New consumers may
instead import `Endpoint.Conjugation` for type-valued Hom sheaves or
`Automorphism` for commutative automorphism-group sheaves.
-/
