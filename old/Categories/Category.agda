{-# OPTIONS --cubical  #-}
{-

  In spirit of this 'prelude' being more focussed writing programs than proofs,
  the categories defined here lack laws, and also aren't categories in the
  strict homotopical sense. They are what UniMath call Precategories, where
  both the Objects and the Homs can be Types of any H-Level.


  The Motivation behind this is that, with a weaker, but less cumbersome notion of categories,
  they can be useful for building up the standard language of functinoal programming,
  in a slightly more general way. With the additional benifit of being able to reuse a
  lot of notation.

-}
module Categories.Category where

open import Categories.Category.Base public
