extern crate slab;


use self::slab::Slab;
use std::cell::{Ref, RefCell, RefMut};
use std::ops::{Deref, DerefMut};
use std::rc::Rc;


pub struct ObjectPool<T> {
    pool: Rc<RefCell<Slab<T>>>,
}

impl<T> ObjectPool<T> {

    pub fn new() -> ObjectPool<T> {
        ObjectPool { pool: Rc::new(RefCell::new(Slab::new())) }
    }

    pub fn insert(&self, obj: T) -> ObjectKey {
        ObjectKey { id:self.pool.borrow_mut().insert(obj) }
    }

    pub fn delete(&self, key: ObjectKey) -> T {
        self.pool.borrow_mut().remove(key.id)
    }

    pub fn get(&self, key: ObjectKey) -> Object<T> {
        Object { pool: self.pool.borrow(), key }
    }

    pub fn get_mut(&self, key: ObjectKey) -> ObjectMut<T> {
        ObjectMut { pool: self.pool.borrow_mut(), key }
    }
}

pub struct ObjectKey {
    id: usize,
}

pub struct Object<'a, T: 'a> {
    pool: Ref<'a, Slab<T>>,
    key:  ObjectKey,
}

pub struct ObjectMut<'a, T: 'a> {
    pool: RefMut<'a, Slab<T>>,
    key:  ObjectKey,
}

impl<'a, T> Deref for Object<'a, T> {

    type Target = T;

    fn deref(&self) -> &T {
        &self.pool[self.key.id]
    }
}

impl<'a, T> Deref for ObjectMut<'a, T> {

    type Target = T;

    fn deref(&self) -> &T {
        &self.pool[self.key.id]
    }
}

impl<'a, T> DerefMut for ObjectMut<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.pool[self.key.id]
    }
}
