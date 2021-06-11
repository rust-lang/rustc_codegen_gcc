#![feature(array_chunks, slice_as_chunks)]

fn main() {
    let v: &mut [i32] = &mut [0, 1, 2, 3, 4, 5, 6];

    const WINDOW_SIZE: usize = 3;

    let mut i = 0;
    let len = v.len();
    while i < len {
        if i + WINDOW_SIZE >= len {
            break;
        }

        //let slice: &mut [i32; WINDOW_SIZE] = TryFrom::try_from(&mut v[i..i+WINDOW_SIZE]).unwrap();
        let slice = &mut v[i..i+WINDOW_SIZE];
        let ptr = slice.as_mut_ptr() as *mut [i32; WINDOW_SIZE];
        let array: &mut [i32; WINDOW_SIZE] = unsafe { &mut *ptr };
        //println!("{:?}", array);

        let sum = array.iter().sum::<i32>();
        *array = [sum; WINDOW_SIZE];

        i += WINDOW_SIZE;
    }

    //println!("{:?}", v);
    assert_eq!(v, &[3, 3, 3, 12, 12, 12, 6]);

    /*for a in v.array_chunks_mut() {
        let sum = a.iter().sum::<i32>();
        *a = [sum; 3];
    }
    assert_eq!(v, &[3, 3, 3, 12, 12, 12, 6]);*/

    /*let v2: &mut [i32] = &mut [0, 1, 2, 3, 4, 5, 6];
    v2.array_chunks_mut().for_each(|[a, b]| core::mem::swap(a, b));
    assert_eq!(v2, &[1, 0, 3, 2, 5, 4, 6]);*/
}
