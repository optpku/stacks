module

public import ReasLib.CategoryTheory.Functor.IndexedProduct.Functoriality
public import ReasLib.CategoryTheory.Functor.IndexedProduct.Op
public import ReasLib.CategoryTheory.Functor.IndexedProduct.HomFamily
public import ReasLib.CategoryTheory.Functor.IndexedProduct.Op.HomFamily

/-!
# Indexed products

Compatibility umbrella for both variance orientations of indexed products.

Import `IndexedProduct.Basic` for existence classes only,
`IndexedProduct.Functoriality` for `Functor.indexedProd`, `IndexedProduct.Op`
for `Functor.indexedProd.op`, or this umbrella for the compatible-family universal properties
in both variance orientations.
-/
