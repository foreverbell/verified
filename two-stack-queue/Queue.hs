module Queue where

import qualified Prelude

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

rev :: (([]) a1) -> ([]) a1
rev l =
  case l of {
   ([]) -> ([]);
   (:) x l' -> app (rev l') ((:) x ([]))}

type A = Prelude.Int

type Stack a = ([]) a

type Queue = (,) (Stack A) (Stack A)

empty :: Queue
empty =
  (,) ([]) ([])

is_empty :: Queue -> Prelude.Bool
is_empty q =
  case q of {
   (,) s _ -> case s of {
               ([]) -> Prelude.True;
               (:) _ _ -> Prelude.False}}

front :: Queue -> Prelude.Maybe A
front q =
  case q of {
   (,) s _ -> case s of {
               ([]) -> Prelude.Nothing;
               (:) x _ -> Prelude.Just x}}

enque :: A -> Queue -> Queue
enque x q =
  case q of {
   (,) ys xs -> case ys of {
                 ([]) -> (,) ((:) x ([])) ([]);
                 (:) _ _ -> (,) ys ((:) x xs)}}

deque :: Queue -> Queue
deque q =
  case q of {
   (,) s ys ->
    case s of {
     ([]) -> (,) ([]) ([]);
     (:) _ xs -> case xs of {
                  ([]) -> (,) (rev ys) ([]);
                  (:) _ _ -> (,) xs ys}}}

