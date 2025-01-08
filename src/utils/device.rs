use ocl::core::{DeviceInfo as OclInfo, DeviceInfoResult};
use ocl::{Device, Platform};

pub struct DeviceInfo {
    pub name: String,
    pub platform_name: String,
    pub max_work_group_size: usize,
    pub max_work_item_sizes: Vec<usize>,
    pub max_work_item_dimensions: u32,

    // hold the actual device
    pub device: Device,
}

pub struct DeviceList(pub Vec<DeviceInfo>);

impl DeviceInfo {
    pub fn new(device: Device, platform: Platform) -> anyhow::Result<Self> {
        Ok(Self {
            name: device.name()?,
            platform_name: platform.name()?,
            max_work_group_size: match device.info(OclInfo::MaxWorkGroupSize)? {
                DeviceInfoResult::MaxWorkGroupSize(size) => size,
                _ => unreachable!(),
            },
            max_work_item_sizes: match device.info(OclInfo::MaxWorkItemSizes)? {
                DeviceInfoResult::MaxWorkItemSizes(wgs) => wgs,
                _ => unreachable!(),
            },
            max_work_item_dimensions: match device.info(OclInfo::MaxWorkItemDimensions)? {
                DeviceInfoResult::MaxWorkItemDimensions(dim) => dim,
                _ => unreachable!(),
            },
            device,
        })
    }
}

impl DeviceList {
    pub fn new() -> anyhow::Result<Self> {
        let platforms = Platform::list();
        let mut list = Vec::with_capacity(platforms.len());
        for platform in platforms {
            if let Ok(devices) = Device::list_all(platform) {
                for device in devices {
                    list.push(DeviceInfo::new(device, platform)?);
                }
            }
        }
        Ok(Self(list))
    }
}

impl std::fmt::Debug for DeviceInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{} ({}, MaxWorkGroupSize={}, MaxWorkItemSizes={}, MaxWorkItemDimensions={})",
            self.name,
            self.platform_name,
            self.max_work_group_size,
            self.max_work_item_sizes
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.max_work_item_dimensions
        )
    }
}

impl std::ops::Deref for DeviceList {
    type Target = Vec<DeviceInfo>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::fmt::Debug for DeviceList {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for (index, device) in self.0.iter().enumerate() {
            writeln!(f, "Device #{} - {:?}\n", index, device)?;
        }
        Ok(())
    }
}
