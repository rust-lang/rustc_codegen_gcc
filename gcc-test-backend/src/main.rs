fn i128_to_u64(u: i128) -> Option<u64> {
    let min = u64::MIN as i128;
    //let max = u64::MAX as i128;
    let max = 18446744073709551612_i128;
    //println!("{} < {} => {}", u, min, u < min);
    //println!("max: {:b}", u64::MAX);
    println!("max: {:b}", max);
    println!("max: {}", max);
    //println!("{}", u < min);
    //println!("{}", u > max);
    if u < min || u > max {
        None
    } else {
        Some(u as u64)
    }
}

fn main() {
    use std::convert::TryFrom;

    /*let max = <i128>::MAX;
    let min = <i128>::MIN;*/
    let zero: i128 = 0;
    /*let t_max = <u64>::MAX;
    let t_min = <u64>::MIN;
    assert!(<u64 as TryFrom<i128>>::try_from(max).is_err());
    assert!(<u64 as TryFrom<i128>>::try_from(min).is_err());*/
    println!("{:?}", i128_to_u64(zero));
    assert_eq!(<u64 as TryFrom<i128>>::try_from(zero).unwrap(), zero as u64);
    /*assert_eq!(
        <u64 as TryFrom<i128>>::try_from(t_max as i128).unwrap(),
        t_max as u64
    );
    assert_eq!(
        <u64 as TryFrom<i128>>::try_from(t_min as i128).unwrap(),
        t_min as u64
    );*/
}
