// deqmap::tests
//
//!
//

use crate::{error::Error, DeqMap};

#[test]
fn deqmap() {
    // construct
    let mut qm = DeqMap::new();
    assert_eq![qm.len(), (0, 0)];

    // push keyless
    qm.push_back(2);
    qm.push_back(3);
    qm.push_front(1);
    assert_eq![3, qm.len_values()];
    assert_eq![0, qm.len_keys()];

    // insert keyed
    qm.insert_back("Four", 4);
    qm.insert_front("Zero", 0);
    assert_eq![5, qm.len_values()];
    assert_eq![2, qm.len_keys()];

    // get keyless
    assert_eq![Ok(&0), qm.get(0)];
    assert_eq![Ok(&4), qm.get(4)];
    assert_eq![Err(Error::IndexOutOfBounds), qm.get(6)];

    // get keyed
    assert_eq![Some(&4), qm.get_keyed("Four")];
    assert_eq![None, qm.get_keyed("Nonexistant")];
}

#[test]
fn deqmap_swap() {
    let mut qm = DeqMap::new();
    qm.insert_back("0", 0);
    qm.insert_back("1", 1);
    qm.insert_back("2", 2);

    assert![qm.swap(4, 0).is_err()];
    assert![qm.swap(0, 4).is_err()];
    qm.swap_unchecked(1, 2);

    let mut i = qm.iter();
    assert_eq![Some(&0), i.next()];
    assert_eq![Some(&2), i.next()];
    assert_eq![Some(&1), i.next()];
}

#[test]
fn deqmap_iter() {
    let mut qm = DeqMap::new();
    qm.insert_back("a", 0);
    qm.insert_back("b", 1);
    qm.push_back(2);

    let mut i = qm.iter();
    assert_eq![Some(&0), i.next()];
    assert_eq![Some(&1), i.next()];
    assert_eq![Some(&2), i.next()];
    assert_eq![None, i.next()];

    let mut i = qm.iter_with_keys();
    assert_eq![Some((Some(&"a"), &0)), i.next()];
    assert_eq![Some((Some(&"b"), &1)), i.next()];
    assert_eq![Some((None, &2)), i.next()];
    assert_eq![None, i.next()];
}
